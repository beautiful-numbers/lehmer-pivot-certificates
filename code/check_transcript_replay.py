#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
check_transcript_replay.py

Deterministic replay checker for a machine-checkable Appendix C transcript.

What this checker enforces:
  (i)  Hash-chain integrity: every record carries {hash, prev_hash} and the chain verifies.
  (ii) Coverage: exactly one non-interleaved Y_START(y) ... Y_END(y) block for each prime y in [y_min, y_max).
  (iii) Protocol discipline (minimal, structural):
        - state identity is deterministic: S_ref = H_support(S) if S is present, state_id = H_state(y, S_ref).
        - gate pass/fail are unique per state_id (no duplicates, no pass-after-fail / fail-after-pass).
        - terminal requires prior gate_pass and a saturation certificate token field.
        - optional bootstrap gating: if a record asserts uses_closure=True at (y,W), it must be preceded by BOOTSTRAP_PASS(y,W).
  (iv) Closure: at Y_END(y), every state opened in that y-block must be closed.
  (v) Optional: exact leaf arithmetic checks for records that provide support S plus a declared result.

Transcript expectations (replay format):
  - JSONL: one JSON object per line.
  - Every record must contain:
      type (string), y (int), hash (hex), prev_hash (hex).
  - State-bearing records must contain either:
      S (list[int]) or S_ref/support_ref (hex), and optionally state_id (hex).
    If state_id is absent it is derived as H_state(y, S_ref).
  - To prove "all branches closed", your transcript must emit:
      STATE_OPEN and STATE_CLOSE records (names configurable via CLI).

Run:
  python3 code/check_transcript_replay.py certificates/appendixC/transcript_replay.jsonl \
      --summary certificates/appendixC/summary_replay.json

Exit codes:
  PASS (0) / FAIL (1)
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Set, Tuple


# ---------------------------
# Errors
# ---------------------------

class CheckError(Exception):
    pass


# ---------------------------
# Hashing & canonicalization
# ---------------------------

def sha256_hex(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def canonical_record_bytes(rec: dict) -> bytes:
    """
    Canonical JSON serialization for hash-binding.

    We hash the record with the 'hash' field omitted.
    """
    if not isinstance(rec, dict):
        raise CheckError("Record must be a JSON object")
    tmp = dict(rec)
    tmp.pop("hash", None)
    tmp.pop("_lineno", None)
    s = json.dumps(tmp, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return s.encode("utf-8")


def as_hex(x) -> str:
    if isinstance(x, bytes):
        return x.hex()
    if isinstance(x, str):
        s = x.strip().lower()
        if s.startswith("0x"):
            s = s[2:]
        return s
    raise CheckError(f"Expected hex string/bytes, got {type(x)}")


def require_hex(label: str, hx: str, strict_len: bool) -> str:
    hx = hx.strip().lower()
    if not hx:
        raise CheckError(f"{label} is empty")
    if any(c not in "0123456789abcdef" for c in hx):
        raise CheckError(f"{label} is not valid hex: {hx!r}")
    if strict_len and len(hx) != 64:
        raise CheckError(f"{label} must be 32-byte hex (64 chars), got len={len(hx)}")
    return hx


# ---------------------------
# State identity layer
# ---------------------------

def normalize_support(S: List[int]) -> List[int]:
    if not isinstance(S, list) or len(S) == 0:
        raise CheckError("Support S must be a non-empty list[int]")
    S2 = sorted(int(x) for x in S)
    if len(S2) != len(set(S2)):
        raise CheckError(f"Support has duplicates: {S}")
    if any(p <= 2 or p % 2 == 0 for p in S2):
        raise CheckError(f"Support contains non-odd-prime entries: {S}")
    return S2


def H_support(S: List[int]) -> str:
    """Canonical support hash (hex)."""
    S2 = normalize_support(S)
    payload = "S|" + ",".join(str(p) for p in S2)
    return sha256_hex(payload.encode("utf-8"))


def H_state(y: int, S_ref_hex: str) -> str:
    """Canonical state hash (hex)."""
    payload = f"STATE|{int(y)}|{S_ref_hex.lower()}"
    return sha256_hex(payload.encode("utf-8"))


def get_y(rec: dict) -> int:
    if "y" not in rec:
        raise CheckError("Missing field 'y'")
    return int(rec["y"])


def get_state_fields(rec: dict, strict_len: bool) -> Tuple[int, str, str]:
    """
    Return (y, S_ref_hex, state_id_hex), all lowercase hex.

    Validates:
      - state_id matches recomputation from (y,S_ref)
      - if S is present, S_ref matches H_support(S)
    """
    y = get_y(rec)

    if "S_ref" in rec:
        S_ref = as_hex(rec["S_ref"])
    elif "support_ref" in rec:
        S_ref = as_hex(rec["support_ref"])
    elif "S" in rec:
        S_ref = H_support(rec["S"])
    else:
        raise CheckError("State-bearing record must include 'S' or 'S_ref'/'support_ref'")

    S_ref = require_hex("S_ref", S_ref, strict_len)

    if "state_id" in rec:
        sid = as_hex(rec["state_id"])
    else:
        sid = H_state(y, S_ref)

    sid = require_hex("state_id", sid, strict_len)

    expected_sid = H_state(y, S_ref)
    if sid != expected_sid:
        raise CheckError(f"state_id mismatch: got {sid}, expected {expected_sid} for y={y}")

    if "S" in rec:
        expected_S_ref = H_support(rec["S"])
        if expected_S_ref != S_ref:
            raise CheckError(f"S_ref mismatch: got {S_ref}, expected {expected_S_ref} for y={y}")

    return y, S_ref, sid


# ---------------------------
# Primes for completeness
# ---------------------------

def primes_in_range(lo: int, hi: int) -> List[int]:
    if hi <= 2 or hi <= lo:
        return []
    n = hi - 1
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"
    p = 2
    while p * p <= n:
        if sieve[p]:
            step = p
            start = p * p
            sieve[start:n + 1:step] = b"\x00" * (((n - start) // step) + 1)
        p += 1
    return [x for x in range(max(lo, 2), hi) if sieve[x]]


# ---------------------------
# Optional exact arithmetic for leaf checks
# ---------------------------

def prod(vals: Iterable[int]) -> int:
    out = 1
    for v in vals:
        out *= int(v)
    return out


def phi_squarefree_from_primes(primes: List[int]) -> int:
    out = 1
    for p in primes:
        out *= (int(p) - 1)
    return out


# ---------------------------
# Transcript helpers
# ---------------------------

def rtype(rec: dict) -> str:
    t = rec.get("type") or rec.get("kind") or rec.get("tag")
    return str(t).strip().upper() if t is not None else ""


def iter_jsonl(path: Path) -> Iterable[Tuple[int, dict]]:
    try:
        with path.open("r", encoding="utf-8") as f:
            for lineno, line in enumerate(f, start=1):
                s = line.strip()
                if not s or s.startswith("#"):
                    continue
                try:
                    obj = json.loads(s)
                except json.JSONDecodeError as e:
                    raise CheckError(f"{path}:{lineno}: invalid JSON ({e})") from None
                if not isinstance(obj, dict):
                    raise CheckError(f"{path}:{lineno}: expected JSON object")
                yield lineno, obj
    except FileNotFoundError:
        raise CheckError(f"Transcript not found: {path}") from None


# ---------------------------
# Replay Checker
# ---------------------------

@dataclass
class StateInfo:
    y: int
    S_ref: str
    opened: bool = False
    closed: bool = False
    gate_pass: bool = False
    gate_fail: bool = False
    terminal: bool = False


class ReplayChecker:
    def __init__(
        self,
        y_min: int,
        y_max: int,
        strict: bool = False,
        verify_leaf_math: bool = False,
        # record type mapping
        y_start_type: str = "Y_START",
        y_end_type: str = "Y_END",
        state_open_type: str = "STATE_OPEN",
        state_close_type: str = "STATE_CLOSE",
        bootstrap_pass_type: str = "BOOTSTRAP_PASS",
        gate_pass_type: str = "CASEB_GATE_PASS",
        gate_fail_type: str = "CASEB_GATE_FAIL",
        terminal_type: str = "CASEB_TERMINAL",
        # leaf types
        leaf_type: str = "LEAF",
        exact_check_type: str = "EXACT_CHECK",
    ):
        self.y_min = int(y_min)
        self.y_max = int(y_max)
        self.strict = strict
        self.verify_leaf_math = verify_leaf_math

        self.T_Y_START = y_start_type.upper()
        self.T_Y_END = y_end_type.upper()
        self.T_OPEN = state_open_type.upper()
        self.T_CLOSE = state_close_type.upper()
        self.T_BOOT = bootstrap_pass_type.upper()
        self.T_GATE_PASS = gate_pass_type.upper()
        self.T_GATE_FAIL = gate_fail_type.upper()
        self.T_TERMINAL = terminal_type.upper()
        self.T_LEAF = leaf_type.upper()
        self.T_EXACT = exact_check_type.upper()

        self.expected_primes = primes_in_range(self.y_min, self.y_max)
        self.expected_set = set(self.expected_primes)

        self.started: Set[int] = set()
        self.ended: Set[int] = set()
        self.ended_order: List[int] = []
        self.current_y: Optional[int] = None

        self.prev_hash: Optional[str] = None

        # bootstrap discipline: (y,W) enabled by BOOTSTRAP_PASS
        self.bootstrap_enabled: Set[Tuple[int, int]] = set()

        self.states: Dict[str, StateInfo] = {}
        self.open_states_by_y: Dict[int, Set[str]] = {y: set() for y in self.expected_primes}

    # ---------- state map ----------

    def _get_state(self, sid: str, y: int, S_ref: str) -> StateInfo:
        if sid in self.states:
            st = self.states[sid]
            if st.y != y or st.S_ref != S_ref:
                raise CheckError(
                    f"State collision: state_id={sid} first seen (y,S_ref)=({st.y},{st.S_ref}) "
                    f"now ({y},{S_ref})"
                )
            return st
        st = StateInfo(y=y, S_ref=S_ref)
        self.states[sid] = st
        return st

    # ---------- hash chain ----------

    def _check_hash_chain(self, lineno: int, rec: dict) -> None:
        if "hash" not in rec or "prev_hash" not in rec:
            raise CheckError(f"Line {lineno}: missing 'hash' or 'prev_hash' fields")

        h = require_hex("hash", as_hex(rec["hash"]), self.strict)
        ph = require_hex("prev_hash", as_hex(rec["prev_hash"]), self.strict)

        computed = sha256_hex(canonical_record_bytes(rec))
        if h != computed:
            raise CheckError(
                f"Line {lineno}: record hash mismatch\n"
                f"  got:      {h}\n"
                f"  expected: {computed}"
            )

        if self.prev_hash is None:
            # First record: accept any prev_hash value (recommended: 64 zeros),
            # and start the chain from the computed hash.
            self.prev_hash = h
            return

        if ph != self.prev_hash:
            raise CheckError(
                f"Line {lineno}: prev_hash mismatch\n"
                f"  got prev_hash: {ph}\n"
                f"  expected:      {self.prev_hash}"
            )

        self.prev_hash = h

    # ---------- coverage + closure ----------

    def _require_in_block(self, lineno: int, y: int, t: str) -> None:
        if self.current_y is None:
            raise CheckError(f"Line {lineno}: record type={t} occurs outside any y-block")
        if y != self.current_y:
            raise CheckError(f"Line {lineno}: record type={t} has y={y} but open block y={self.current_y}")

    def _on_y_start(self, lineno: int, y: int) -> None:
        if self.current_y is not None:
            raise CheckError(f"Line {lineno}: Y_START(y={y}) while y={self.current_y} is still open")
        if y not in self.expected_set:
            raise CheckError(f"Line {lineno}: Y_START(y={y}) not in expected primes [{self.y_min},{self.y_max})")
        if y in self.started:
            raise CheckError(f"Line {lineno}: duplicate Y_START for y={y}")
        self.started.add(y)
        self.current_y = y

    def _on_y_end(self, lineno: int, y: int) -> None:
        if self.current_y is None:
            raise CheckError(f"Line {lineno}: Y_END(y={y}) with no open y-block")
        if y != self.current_y:
            raise CheckError(f"Line {lineno}: Y_END(y={y}) does not match open y-block y={self.current_y}")
        if y in self.ended:
            raise CheckError(f"Line {lineno}: duplicate Y_END for y={y}")

        open_set = self.open_states_by_y.get(y, set())
        if open_set:
            sid = next(iter(sorted(open_set)))
            raise CheckError(f"Line {lineno}: Y_END(y={y}) but there are still open states (example state_id={sid})")

        self.ended.add(y)
        self.ended_order.append(y)
        self.current_y = None

    # ---------- bootstrap discipline ----------

    def _on_bootstrap_pass(self, lineno: int, rec: dict) -> None:
        y = get_y(rec)
        self._require_in_block(lineno, y, self.T_BOOT)
        if "W" not in rec:
            raise CheckError(f"Line {lineno}: BOOTSTRAP_PASS missing field 'W'")
        W = int(rec["W"])
        self.bootstrap_enabled.add((y, W))

    def _bootstrap_required_if(self, lineno: int, rec: dict) -> None:
        uses = bool(rec.get("uses_closure", False))
        if not uses:
            return
        y = get_y(rec)
        if "W" not in rec:
            raise CheckError(f"Line {lineno}: uses_closure=True but missing field 'W'")
        W = int(rec["W"])
        if (y, W) not in self.bootstrap_enabled:
            raise CheckError(f"Line {lineno}: uses_closure at (y,W)=({y},{W}) without prior BOOTSTRAP_PASS")

    # ---------- gate/terminal ----------

    def _on_gate_pass(self, lineno: int, rec: dict) -> None:
        y, S_ref, sid = get_state_fields(rec, self.strict)
        self._require_in_block(lineno, y, self.T_GATE_PASS)
        st = self._get_state(sid, y, S_ref)
        if st.gate_fail:
            raise CheckError(f"Line {lineno}: gate_pass after gate_fail for state_id={sid}")
        if st.gate_pass:
            raise CheckError(f"Line {lineno}: duplicate gate_pass for state_id={sid}")
        st.gate_pass = True

    def _on_gate_fail(self, lineno: int, rec: dict) -> None:
        y, S_ref, sid = get_state_fields(rec, self.strict)
        self._require_in_block(lineno, y, self.T_GATE_FAIL)
        st = self._get_state(sid, y, S_ref)
        if st.gate_pass:
            raise CheckError(f"Line {lineno}: gate_fail after gate_pass for state_id={sid}")
        if st.gate_fail:
            raise CheckError(f"Line {lineno}: duplicate gate_fail for state_id={sid}")
        st.gate_fail = True

    def _on_terminal(self, lineno: int, rec: dict) -> None:
        y, S_ref, sid = get_state_fields(rec, self.strict)
        self._require_in_block(lineno, y, self.T_TERMINAL)
        st = self._get_state(sid, y, S_ref)
        if not st.gate_pass:
            raise CheckError(f"Line {lineno}: terminal without prior gate_pass for state_id={sid}")
        cert_sat = rec.get("cert_sat") or rec.get("sat_cert") or rec.get("saturation_cert")
        if not cert_sat:
            raise CheckError(f"Line {lineno}: terminal missing saturation certificate for state_id={sid}")
        st.terminal = True

    # ---------- open/close ----------

    def _on_state_open(self, lineno: int, rec: dict) -> None:
        y, S_ref, sid = get_state_fields(rec, self.strict)
        self._require_in_block(lineno, y, self.T_OPEN)
        st = self._get_state(sid, y, S_ref)
        if st.opened:
            raise CheckError(f"Line {lineno}: duplicate STATE_OPEN for state_id={sid}")
        if st.closed:
            raise CheckError(f"Line {lineno}: STATE_OPEN after STATE_CLOSE for state_id={sid}")
        st.opened = True
        self.open_states_by_y[y].add(sid)

    def _on_state_close(self, lineno: int, rec: dict) -> None:
        y, S_ref, sid = get_state_fields(rec, self.strict)
        self._require_in_block(lineno, y, self.T_CLOSE)
        st = self._get_state(sid, y, S_ref)
        if not st.opened:
            raise CheckError(f"Line {lineno}: STATE_CLOSE without prior STATE_OPEN for state_id={sid}")
        if st.closed:
            raise CheckError(f"Line {lineno}: duplicate STATE_CLOSE for state_id={sid}")
        st.closed = True
        self.open_states_by_y[y].discard(sid)

    # ---------- optional leaf math ----------

    def _check_leaf_math(self, lineno: int, rec: dict) -> None:
        y = get_y(rec)
        self._require_in_block(lineno, y, rtype(rec))
        if "S" not in rec:
            raise CheckError(f"Line {lineno}: leaf record missing support S")

        S = normalize_support(rec["S"])
        nS = int(rec.get("nS", prod(S)))
        phi_nS = int(rec.get("phi_nS", phi_squarefree_from_primes(S)))

        ok = ((nS - 1) % phi_nS == 0)

        if "result" in rec:
            got = str(rec["result"]).strip().upper()
            exp = "PASS" if ok else "FAIL"
            if got != exp:
                raise CheckError(f"Line {lineno}: leaf result mismatch: got {got}, expected {exp}")
        elif "ok" in rec:
            gotb = bool(rec["ok"])
            if gotb != ok:
                raise CheckError(f"Line {lineno}: leaf ok mismatch: got {gotb}, expected {ok}")
        else:
            raise CheckError(
                f"Line {lineno}: leaf record must include 'result' or 'ok' when --verify-leaf-math is set"
            )

    # ---------- main loop ----------

    def run(self, transcript_path: Path) -> None:
        for lineno, rec in iter_jsonl(transcript_path):
            self._check_hash_chain(lineno, rec)

            t = rtype(rec)
            if not t:
                raise CheckError(f"Line {lineno}: missing record field 'type'/'kind'/'tag'")
            y = get_y(rec)

            if t == self.T_Y_START:
                self._on_y_start(lineno, y)
                continue

            if t == self.T_Y_END:
                self._on_y_end(lineno, y)
                continue

            self._require_in_block(lineno, y, t)
            self._bootstrap_required_if(lineno, rec)

            if t == self.T_OPEN:
                self._on_state_open(lineno, rec)
            elif t == self.T_CLOSE:
                self._on_state_close(lineno, rec)
            elif t == self.T_BOOT:
                self._on_bootstrap_pass(lineno, rec)
            elif t == self.T_GATE_PASS:
                self._on_gate_pass(lineno, rec)
            elif t == self.T_GATE_FAIL:
                self._on_gate_fail(lineno, rec)
            elif t == self.T_TERMINAL:
                self._on_terminal(lineno, rec)
            elif self.verify_leaf_math and (t == self.T_LEAF or t == self.T_EXACT):
                self._check_leaf_math(lineno, rec)
            else:
                # Unknown types are permitted; still covered by:
                #   - hash-chain,
                #   - y-block discipline,
                #   - bootstrap gating when uses_closure=True.
                pass

        if self.current_y is not None:
            raise CheckError(f"EOF: y-block still open for y={self.current_y} (missing Y_END)")

        missing_start = [p for p in self.expected_primes if p not in self.started]
        missing_end = [p for p in self.expected_primes if p not in self.ended]
        if missing_start or missing_end:
            msg = ["Completeness failure:"]
            if missing_start:
                msg.append(f"  missing Y_START for {len(missing_start)} primes (first few {missing_start[:10]})")
            if missing_end:
                msg.append(f"  missing Y_END for {len(missing_end)} primes (first few {missing_end[:10]})")
            raise CheckError("\n".join(msg))

        if self.ended_order != self.expected_primes:
            raise CheckError(
                "Unexpected y closure order.\n"
                f"  expected first 10: {self.expected_primes[:10]}\n"
                f"  got first 10:      {self.ended_order[:10]}"
            )

        leaked = [(y, next(iter(sorted(sids)))) for y, sids in self.open_states_by_y.items() if sids]
        if leaked:
            y0, sid0 = leaked[0]
            raise CheckError(f"Leaked open states after EOF (example y={y0}, state_id={sid0})")

        for sid, st in self.states.items():
            if st.opened and not st.closed:
                raise CheckError(f"State opened but not closed: state_id={sid} (y={st.y})")


# ---------------------------
# CLI
# ---------------------------

def load_summary_range(summary_path: Path) -> Tuple[int, int]:
    try:
        data = json.loads(summary_path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        raise CheckError(f"Summary not found: {summary_path}") from None
    except json.JSONDecodeError as e:
        raise CheckError(f"Invalid JSON summary: {summary_path} ({e})") from None

    params = data.get("params", {})
    if not isinstance(params, dict):
        raise CheckError(f"summary.json: missing/invalid params dict in {summary_path}")
    y_min = params.get("y_min")
    y_max = params.get("y_max")
    if not isinstance(y_min, int) or not isinstance(y_max, int):
        raise CheckError(f"summary.json: params.y_min/y_max must be integers in {summary_path}")
    return int(y_min), int(y_max)


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description="Deterministic replay checker for Appendix C transcript_replay.jsonl.")
    ap.add_argument("transcript", type=Path, help="Replay transcript JSONL (machine-checkable).")
    ap.add_argument("--summary", type=Path, default=None, help="Summary JSON providing params.y_min/y_max.")
    ap.add_argument("--y-min", type=int, default=None, help="Override y_min if no summary is provided.")
    ap.add_argument("--y-max", type=int, default=None, help="Override y_max if no summary is provided.")
    ap.add_argument("--strict", action="store_true", help="Require 64-hex length for all hash fields.")
    ap.add_argument("--verify-leaf-math", action="store_true", help="Verify leaf/exact-check divisibility if present.")

    ap.add_argument("--y-start-type", default="Y_START")
    ap.add_argument("--y-end-type", default="Y_END")
    ap.add_argument("--state-open-type", default="STATE_OPEN")
    ap.add_argument("--state-close-type", default="STATE_CLOSE")
    ap.add_argument("--bootstrap-pass-type", default="bootstrap_pass")
    ap.add_argument("--gate-pass-type", default="caseB_gate_pass")
    ap.add_argument("--gate-fail-type", default="caseB_gate_fail")
    ap.add_argument("--terminal-type", default="caseB_terminal")
    ap.add_argument("--leaf-type", default="LEAF")
    ap.add_argument("--exact-check-type", default="EXACT_CHECK")

    args = ap.parse_args(argv)

    if args.summary is not None:
        y_min, y_max = load_summary_range(args.summary)
    else:
        if args.y_min is None or args.y_max is None:
            print("FAIL: must provide --summary or both --y-min and --y-max", file=sys.stderr)
            return 1
        y_min, y_max = int(args.y_min), int(args.y_max)

    try:
        ck = ReplayChecker(
            y_min=y_min,
            y_max=y_max,
            strict=args.strict,
            verify_leaf_math=args.verify_leaf_math,
            y_start_type=args.y_start_type,
            y_end_type=args.y_end_type,
            state_open_type=args.state_open_type,
            state_close_type=args.state_close_type,
            bootstrap_pass_type=args.bootstrap_pass_type,
            gate_pass_type=args.gate_pass_type,
            gate_fail_type=args.gate_fail_type,
            terminal_type=args.terminal_type,
            leaf_type=args.leaf_type,
            exact_check_type=args.exact_check_type,
        )
        ck.run(args.transcript)
    except CheckError as e:
        print(f"FAIL: {e}", file=sys.stderr)
        return 1

    print("PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
