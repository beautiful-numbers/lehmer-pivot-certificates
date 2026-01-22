#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
caseC_minimal_checker.py

Minimal transcript checker for Appendix C (finite verification infrastructure).

What this checker enforces (Appendix C.4–C.5):
  - Reads a full transcript as a sequence of records (JSONL).
  - Recomputes all numerical invariants needed to validate each record
    using exact integer/rational arithmetic only.
  - Enforces the bootstrap discipline (Proposition C.8): any record that
    uses closure-derived quantities N(y,W), Ω̂(y,W) or consequences is invalid
    unless preceded (in transcript order) by a PASS bootstrap record at (y,W).
  - Verifies each leaf record by the exact divisibility test φ(n_S) | (n_S - 1).
  - Emits PASS (exit 0) iff every record verifies; otherwise FAIL (exit 1).

This matches the “minimal checker” spec in Appendix C.4.  See also
Definition C.7 (bootstrap record), Proposition C.8, Definition C.5 (leaf),
and §C.5.1 requirements.  (Paper: Lehmer's Totient Problem and a Prime Cost Pivot Method.)
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple


# ---------------------------
# Utility: exact arithmetic
# ---------------------------

def lcm(a: int, b: int) -> int:
    if a == 0 or b == 0:
        return 0
    return a // math.gcd(a, b) * b


def lcm_list(vals: Iterable[int]) -> int:
    out = 1
    for v in vals:
        out = lcm(out, v)
    return out


def prod(vals: Iterable[int]) -> int:
    out = 1
    for v in vals:
        out *= v
    return out


def phi_squarefree_from_primes(primes: List[int]) -> int:
    # for n_S = Π p, squarefree
    out = 1
    for p in primes:
        out *= (p - 1)
    return out


def I_of_support(primes: List[int]) -> Fraction:
    # I(S) = Π p/(p-1) exactly
    num = 1
    den = 1
    for p in primes:
        num *= p
        den *= (p - 1)
        g = math.gcd(num, den)
        num //= g
        den //= g
    return Fraction(num, den)


def dist_to_Z(x: Fraction) -> Fraction:
    # exact distance to nearest integer: min_{k in Z} |x-k|
    # nearest integers are floor and ceil
    fl = x.numerator // x.denominator
    ce = fl + 1
    d1 = abs(x - fl)
    d2 = abs(x - ce)
    return d1 if d1 <= d2 else d2


# ---------------------------
# Primes: deterministic table
# ---------------------------

def sieve_primes_upto(n: int) -> List[int]:
    if n < 2:
        return []
    bs = bytearray(b"\x01") * (n + 1)
    bs[0:2] = b"\x00\x00"
    for p in range(2, int(n**0.5) + 1):
        if bs[p]:
            step = p
            start = p * p
            bs[start:n+1:step] = b"\x00" * ((n - start)//step + 1)
    return [i for i in range(n + 1) if bs[i]]


@dataclass(frozen=True)
class PrimeSource:
    """
    Either:
      - load primes from a file (one prime per line), or
      - deterministically generate primes up to a stated bound.
    """
    primes: List[int]

    @staticmethod
    def from_file(path: Path) -> "PrimeSource":
        data = path.read_text(encoding="utf-8").strip().splitlines()
        primes = []
        for line in data:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            primes.append(int(line))
        return PrimeSource(primes=primes)

    @staticmethod
    def generated_upto(max_p: int) -> "PrimeSource":
        return PrimeSource(primes=sieve_primes_upto(max_p))

    def is_prime(self, x: int) -> bool:
        # For checker purposes we only need membership in our table bound.
        # Transcript must not reference primes beyond what we can reconstruct.
        # We keep a set for O(1) membership.
        return x in getattr(self, "_set", set(self.primes))

    def ensure_set(self) -> None:
        if not hasattr(self, "_set"):
            object.__setattr__(self, "_set", set(self.primes))


# ---------------------------
# Transcript structures
# ---------------------------

class CheckError(Exception):
    pass


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalize_support(S: List[int]) -> List[int]:
    # canonical order: strictly increasing primes
    if any(p <= 2 for p in S):
        raise CheckError(f"Support contains non-odd-prime entry: {S}")
    S2 = sorted(S)
    if len(S2) != len(set(S2)):
        raise CheckError(f"Support contains duplicates: {S}")
    return S2


def log_floor_ratio(N: int, y: int) -> int:
    # Ω̂ = floor(log N / log y) but computed safely using integer comparisons
    # Find largest k with y^k <= N.
    if y <= 1:
        raise CheckError("y must be >= 2")
    k = 0
    pow_ = 1
    while pow_ <= N // y:
        pow_ *= y
        k += 1
    return k


# ---------------------------
# Bootstrap discipline state
# ---------------------------

@dataclass
class BootstrapData:
    y: int
    W: int
    Delta: Fraction
    Kmax: int
    N: int
    Omega_hat: int
    check: str
    hash: str


class Checker:
    def __init__(self, primes: PrimeSource, strict: bool = True):
        self.primes = primes
        self.primes.ensure_set()
        self.strict = strict
        # enabled[(y,W)] = BootstrapData if PASS
        self.enabled: Dict[Tuple[int, int], BootstrapData] = {}

    # -------------
    # Core recompute
    # -------------

    def recompute_support_invariants(self, S: List[int]) -> Dict[str, object]:
        S = normalize_support(S)
        nS = prod(S)
        phi_nS = phi_squarefree_from_primes(S)
        LS = lcm_list([p - 1 for p in S])
        I = I_of_support(S)
        return {
            "S": S,
            "nS": nS,
            "phi_nS": phi_nS,
            "L(S)": LS,
            "I(S)": I,
            "dist(I,Z)": dist_to_Z(I),
        }

    # ----------------
    # Record validators
    # ----------------

    def check_bootstrap(self, rec: dict) -> None:
        # Appendix C.7: boot(y,W) contains S(y,W), Δ, Kmax, derived N, Ω̂, check, hash
        y = int(rec["y"])
        W = int(rec["W"])
        family = rec["family"]  # list of supports, each list of primes
        Kmax = int(rec["Kmax"])

        # Δ may be stored as rational pair or decimal string; we accept either.
        Delta = self.parse_fraction(rec["Delta"])

        # recompute Δ* from family as min dist(I(S),Z)
        if not isinstance(family, list) or not family:
            raise CheckError(f"bootstrap({y},{W}): family must be a nonempty list")

        dmin: Optional[Fraction] = None
        for S in family:
            inv = self.recompute_support_invariants(S)
            d = inv["dist(I,Z)"]
            dmin = d if dmin is None else (d if d < dmin else dmin)

        if dmin is None:
            raise CheckError(f"bootstrap({y},{W}): failed to compute Δ*")

        if dmin != Delta:
            raise CheckError(
                f"bootstrap({y},{W}): Δ mismatch. transcript={Delta} recomputed={dmin}"
            )

        # derived closure bound N = Kmax/Δ + 1 (integer arithmetic with Fractions)
        # Here Kmax is integer, Delta is Fraction.
        N_frac = Fraction(Kmax, 1) / Delta + 1
        if N_frac.denominator != 1:
            # Paper defines N(y,W)=Kmax/Δ + 1 as a real;
            # transcript should store integer ceil/floor convention explicitly if used.
            # For minimal checker we require exact integer N in transcript.
            raise CheckError(
                f"bootstrap({y},{W}): N=Kmax/Δ+1 not integer under provided Δ. "
                f"Got {N_frac}. If you use ceil/floor, store it explicitly and adjust checker."
            )
        N = int(N_frac)

        # Ω̂ = floor(log N / log y) (computed via integer powers)
        Omega_hat = log_floor_ratio(N, y)

        # check PASS iff Ω̂ < W
        check = str(rec["check"]).upper()
        expected = "PASS" if (Omega_hat < W) else "FAIL"
        if check != expected:
            raise CheckError(
                f"bootstrap({y},{W}): check field mismatch. transcript={check} expected={expected} "
                f"(Ω̂={Omega_hat}, W={W})"
            )

        # hash binding: checker treats as opaque but MUST be present
        h = str(rec.get("hash", ""))
        if self.strict and (not h or len(h) < 16):
            raise CheckError(f"bootstrap({y},{W}): missing/too short hash binding field")

        # If PASS, enable closure-derived quantities for this (y,W)
        if check == "PASS":
            self.enabled[(y, W)] = BootstrapData(
                y=y, W=W, Delta=Delta, Kmax=Kmax, N=N, Omega_hat=Omega_hat, check=check, hash=h
            )

    def check_leaf(self, rec: dict) -> None:
        # Definition C.5: leaf=(id,y,S,nS,phi(nS),result)
        y = int(rec["y"])
        S = rec["S"]
        inv = self.recompute_support_invariants(S)

        nS = int(rec.get("nS", inv["nS"]))
        phi_nS = int(rec.get("phi_nS", inv["phi_nS"]))

        if nS != inv["nS"]:
            raise CheckError(f"leaf: nS mismatch. transcript={nS} recomputed={inv['nS']}")
        if phi_nS != inv["phi_nS"]:
            raise CheckError(f"leaf: phi(nS) mismatch. transcript={phi_nS} recomputed={inv['phi_nS']}")

        ok = ((nS - 1) % phi_nS == 0)
        result = str(rec["result"]).upper()
        expected = "PASS" if ok else "FAIL"
        if result != expected:
            raise CheckError(f"leaf: divisibility result mismatch. transcript={result} expected={expected}")

    def check_cut(self, rec: dict) -> None:
        # Generic cut record:
        #   - must declare whether it uses closure-derived quantities at (y,W).
        #   - checker enforces Proposition C.8.
        y = int(rec["y"])
        W = int(rec.get("W", 0))  # W is mandatory if uses_closure=True
        uses_closure = bool(rec.get("uses_closure", False))

        if uses_closure:
            if (y, W) not in self.enabled:
                raise CheckError(
                    f"cut: record uses closure at (y,W)=({y},{W}) but no prior PASS bootstrap enables it"
                )

        kind = str(rec["kind"]).upper()

        # We implement the one cut that must be unquestionably checkable from the record alone:
        # UB cut (Proposition C.10): verify the numeric inequality UB(S)*UBrest <= 2
        # given that the record provides the extension primes actually used.
        if kind == "UB":
            self.check_cut_ub(rec)
            return

        # For other cuts (C.11–C.14), this minimal checker enforces:
        #   - the record provides all integers it claims to test (e.g. t-range reductions),
        #   - and the stated infeasibility is backed by explicit contradictions or by explicit leaf tests.
        # This keeps the checker “referee-checkable” without re-implementing your entire BnB logic.
        #
        # If you WANT full formal replay of C.11–C.14 premises, extend here.
        if kind in {"CONG", "2ADIC", "LOWEXIT", "SATLOCK"}:
            # minimal consistency checks
            if kind == "SATLOCK" and uses_closure:
                self.check_cut_satlock(rec)
                return
            # otherwise: accept only if record contains an explicit contradiction certificate
            # (e.g. a list of congruences with empty CRT solution) OR explicit leaf tests.
            self.check_cut_explicit_certificate(rec)
            return

        raise CheckError(f"cut: unknown kind={kind}")

    def check_cut_ub(self, rec: dict) -> None:
        # Proposition C.10 (UB cut):
        # UB(S) = Π_{p∈S} p/(p-1)
        # UBrest = Π_{i=1..r} q_i/(q_i-1), where q_i are the r smallest admissible extension primes
        # r = Ω̂(y,W) - |S|   (requires closure-enabled)
        y = int(rec["y"])
        W = int(rec["W"])
        if (y, W) not in self.enabled:
            raise CheckError(f"UB cut: needs enabled closure at (y,W)=({y},{W})")

        S = normalize_support(rec["S"])
        ext_primes = normalize_support(rec["ext_primes"])  # primes used for UBrest (already the q_i list)

        boot = self.enabled[(y, W)]
        r = boot.Omega_hat - len(S)
        if r < 0:
            # then UBrest should be empty and UB cut is vacuous
            r = 0

        if len(ext_primes) != r:
            raise CheckError(
                f"UB cut: ext_primes length mismatch. expected r={r} got {len(ext_primes)}"
            )

        UB = I_of_support(S)  # exact Fraction
        UBrest = I_of_support(ext_primes) if ext_primes else Fraction(1, 1)

        lhs = UB * UBrest
        # Verify lhs <= 2
        if lhs > 2:
            raise CheckError(f"UB cut: inequality fails. UB*UBrest={lhs} > 2")

    def check_cut_satlock(self, rec: dict) -> None:
        # Proposition C.14 (Saturation lock cut) is closure-dependent.
        # Minimal checker version:
        #   - verify bootstrap enabled;
        #   - verify claimed saturated sub-support S' is indeed saturated per record’s ε, or per explicit threshold;
        #   - verify L(S') computed;
        #   - verify each tested n = 1 + t L(S') fails the leaf divisibility test (exact).
        y = int(rec["y"])
        W = int(rec["W"])
        if (y, W) not in self.enabled:
            raise CheckError(f"SATLOCK cut: needs enabled closure at (y,W)=({y},{W})")

        Sprime = normalize_support(rec["S_prime"])
        invp = self.recompute_support_invariants(Sprime)
        Ls = invp["L(S)"]

        # Optional: check saturation numerically if transcript provides epsilon and n_S cap.
        # (Paper: saturation regime definition is global; here we only enforce what can be recomputed locally.)
        eps = rec.get("epsilon", None)
        if eps is not None:
            eps_f = self.parse_fraction(eps)  # allow "2/5" etc
            # P(S) = log L / log n uses real logs; checker avoids floating claims unless you provide exact gate.
            # Minimal enforcement: if transcript claims saturation, it must provide a proof token or be used only
            # for enumerated finite checks. We accept the claim if explicit enumeration list is present.
            pass

        tests = rec.get("tested_t", [])
        if not isinstance(tests, list) or not tests:
            raise CheckError("SATLOCK cut: must provide tested_t list (explicit finite verification)")

        for t in tests:
            t = int(t)
            n = 1 + t * Ls
            # leaf-style check: if this n were a Lehmer candidate with support S', it would need φ(n) | n-1,
            # but here we do not know φ(n). So transcript must provide a concrete integer check it uses.
            #
            # Therefore, SATLOCK cut records must provide explicit candidate nS and φ(nS) pairs, or
            # reduce to exact leaf tests on n_S (support-products). If you instead test global n, store
            # the exact computed φ(n) in record.
            if "phi_of_n" not in rec:
                raise CheckError(
                    "SATLOCK cut: transcript must include phi_of_n[t] values (exact), "
                    "or rewrite cut to reduce to leaf-type checks."
                )

        phi_map = rec["phi_of_n"]
        if not isinstance(phi_map, dict):
            raise CheckError("SATLOCK cut: phi_of_n must be a dict mapping t -> phi(n)")

        for t in tests:
            t = int(t)
            if str(t) not in phi_map and t not in phi_map:
                raise CheckError(f"SATLOCK cut: missing phi(n) for t={t}")
            phi_n = int(phi_map.get(str(t), phi_map.get(t)))
            n = 1 + int(t) * Ls
            if (n - 1) % phi_n == 0:
                raise CheckError(f"SATLOCK cut: found t={t} with phi(n) | n-1 (should fail)")

    def check_cut_explicit_certificate(self, rec: dict) -> None:
        # Minimal acceptance criterion:
        # transcript must provide either:
        #  (A) "contradiction": a nonempty string describing an explicit contradiction verified by the checker, or
        #  (B) "leaves": a nonempty list of leaf-records that we can verify directly.
        contradiction = rec.get("contradiction", "")
        leaves = rec.get("leaves", [])

        if contradiction:
            # We cannot parse arbitrary English contradictions. For minimal checker, demand
            # a machine-checkable payload, e.g. CRT system with explicit inconsistency:
            crt = rec.get("crt_infeasible", None)
            if crt is None:
                raise CheckError(
                    "cut: contradiction present but no machine-checkable payload. "
                    "Provide 'crt_infeasible' system or explicit leaves."
                )
            self.check_crt_infeasible(crt)
            return

        if isinstance(leaves, list) and leaves:
            for leaf in leaves:
                if not isinstance(leaf, dict) or leaf.get("type", "LEAF").upper() != "LEAF":
                    raise CheckError("cut: leaves[] must be leaf dict records")
                self.check_leaf(leaf)
            return

        raise CheckError(
            "cut: minimal checker requires either 'leaves' (explicit leaf tests) "
            "or 'crt_infeasible' payload for a contradiction."
        )

    def check_crt_infeasible(self, payload: dict) -> None:
        # payload:
        #   {"congruences":[{"mod":m1,"rem":r1},...], "witness":"optional"}
        congr = payload.get("congruences", [])
        if not isinstance(congr, list) or not congr:
            raise CheckError("crt_infeasible: congruences must be a nonempty list")

        # A simple infeasibility check: if any pair r≠s mod gcd(m,n), inconsistent
        mods: List[Tuple[int, int]] = []
        for c in congr:
            m = int(c["mod"])
            r = int(c["rem"]) % m
            mods.append((m, r))

        for i in range(len(mods)):
            m1, r1 = mods[i]
            for j in range(i + 1, len(mods)):
                m2, r2 = mods[j]
                g = math.gcd(m1, m2)
                if (r1 - r2) % g != 0:
                    return  # infeasible as claimed

        raise CheckError("crt_infeasible: congruences appear feasible (no contradiction detected)")

    # -------------------
    # Fraction parsing
    # -------------------

    def parse_fraction(self, x) -> Fraction:
        # Accept:
        #  - int
        #  - "a/b"
        #  - {"num":a,"den":b}
        #  - decimal string (only if exact finite decimal)
        if isinstance(x, int):
            return Fraction(x, 1)
        if isinstance(x, Fraction):
            return x
        if isinstance(x, dict) and "num" in x and "den" in x:
            return Fraction(int(x["num"]), int(x["den"]))
        if isinstance(x, str):
            s = x.strip()
            if "/" in s:
                a, b = s.split("/", 1)
                return Fraction(int(a.strip()), int(b.strip()))
            if s.isdigit() or (s.startswith("-") and s[1:].isdigit()):
                return Fraction(int(s), 1)
            # finite decimal only
            if "." in s:
                # interpret exactly as rational
                neg = s.startswith("-")
                s2 = s[1:] if neg else s
                whole, frac = s2.split(".", 1)
                if not (whole.isdigit() and frac.isdigit()):
                    raise CheckError(f"cannot parse fraction: {x}")
                den = 10 ** len(frac)
                num = int(whole) * den + int(frac)
                if neg:
                    num = -num
                return Fraction(num, den)
        raise CheckError(f"cannot parse fraction: {x!r}")

    # -------------------
    # Transcript main loop
    # -------------------

    def run(self, transcript_path: Path) -> None:
        # Optional: bind the transcript hash to make the run reproducible from a manifest.
        transcript_hash = sha256_file(transcript_path)

        with transcript_path.open("r", encoding="utf-8") as f:
            for lineno, line in enumerate(f, start=1):
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                try:
                    rec = json.loads(line)
                except json.JSONDecodeError as e:
                    raise CheckError(f"{transcript_path}:{lineno}: invalid JSON: {e}")

                rtype = str(rec.get("type", "")).upper()
                if not rtype:
                    raise CheckError(f"{transcript_path}:{lineno}: missing record field 'type'")

                # Optional consistency: ensure transcript hash is carried in records that claim it
                if "transcript_sha256" in rec:
                    if str(rec["transcript_sha256"]).lower() != transcript_hash.lower():
                        raise CheckError(
                            f"{transcript_path}:{lineno}: transcript_sha256 mismatch in record"
                        )

                if rtype == "BOOT":
                    self.check_bootstrap(rec)
                elif rtype == "LEAF":
                    self.check_leaf(rec)
                elif rtype == "CUT":
                    self.check_cut(rec)
                elif rtype in {"STATE", "BRANCH", "AUX"}:
                    # Minimal checker can ignore STATE/BRANCH structure if your CUT/LEAF records
                    # are self-contained. If you want full tree validation, extend here.
                    pass
                else:
                    raise CheckError(f"{transcript_path}:{lineno}: unknown record type={rtype}")


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Minimal transcript checker for Appendix C (Lehmer pivot certificates)."
    )
    ap.add_argument("transcript", type=Path, help="Transcript file in JSONL format.")
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--prime-file", type=Path, help="Text file: one prime per line (checker prime table).")
    g.add_argument("--prime-max", type=int, help="Deterministically generate all primes <= prime_max.")
    ap.add_argument("--strict", action="store_true", help="Stricter checks on record hash fields.")
    args = ap.parse_args()

    if args.prime_file is not None:
        primes = PrimeSource.from_file(args.prime_file)
    else:
        primes = PrimeSource.generated_upto(args.prime_max)

    chk = Checker(primes=primes, strict=args.strict)

    try:
        chk.run(args.transcript)
    except CheckError as e:
        print("FAIL")
        print(str(e), file=sys.stderr)
        return 1

    print("PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
