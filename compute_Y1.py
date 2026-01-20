# compute_Y1.py
# -*- coding: utf-8 -*-
"""
compute_Y1.py

Goal:
  Compute a certified (or closed-form) lower bound mreq(y) (pivot) and compare against an upper bound
  M(y)=Wy+Kmax under either:
    - Legacy fixed cap: Ny (window-dependent)
    - Closed-form cap:  N(y) given by an explicit formula (or an explicit finite table y->logN)

Key properties:
  1) FAIL-fast behavior:
       - If prime_limit is insufficient to certify mreq(y) in exact mode: return FAIL_PRIME_LIMIT (no crash).
       - If bounds are too loose to prove minimality with current series terms: return FAIL_AMBIG.
       - If analytic mode is requested below validity threshold Y0: return FAIL_BELOW_Y0 (no crash).
  2) "Hybrid" pivot:
       - Try exact first; if it fails and y>=Y0, fall back to analytic lower bound mreq_lb(y).
       - This is meant for global paper tables where exact mreq(y) is infeasible at large y.

Additions (DO NOT REMOVE legacy modes):
  - mode=pivotA:
      Print traceable constants for Appendix A (Mertens + nth-prime) and a SHA256 hash of the printed report.
  - mode=pivot_only:
      Print a pivot-only table (y, mreq_status, mreq(y)) + SHA256 hash (for Appendix A tables).
  - mode=pivotA_proof:
      Appendix A Step-4 endpoint check with the *correct* Mertens usage (difference, not the crude discard).
      Assumes a published explicit *two-sided* bound of the form:
         | sum_{p<=x} 1/p - (log log x + B1) | <= c/log x   (x >= x0)
      Then:
         sum_{y<=p<=x} 1/p <= (log log x - log log y) + c/log x + c/log y.
      Prints a traceable report + SHA256 hash.
  - Legacy modes remain:
      mode=window  : print full table + first-hit Y1
      mode=caseB   : print full table + stable suffix-Y1

Natural logs throughout.
"""

from __future__ import annotations

import argparse
import bisect
import csv
import hashlib
import math
from dataclasses import dataclass
from decimal import Decimal, getcontext
from typing import Dict, List, Optional, Tuple


# ---------------------------
# Prime sieve
# ---------------------------

def sieve_primes(n: int) -> List[int]:
    if n < 2:
        return []
    bs = bytearray(b"\x01") * (n + 1)
    bs[0:2] = b"\x00\x00"
    lim = int(n ** 0.5)
    for p in range(2, lim + 1):
        if bs[p]:
            start = p * p
            step = p
            bs[start:n + 1:step] = b"\x00" * (((n - start) // step) + 1)
    return [i for i, v in enumerate(bs) if v]


# ---------------------------
# Certified log bounds (used for exact mreq certification)
# ---------------------------

def ln1p_bounds_alt(x: Decimal, n_terms: int) -> Tuple[Decimal, Decimal]:
    """
    Certified bounds for ln(1+x) on 0 < x <= 1/2 using the alternating series:
      ln(1+x) = x - x^2/2 + x^3/3 - x^4/4 + ...
    Truncation error bounded by first omitted term magnitude.
    """
    if x <= 0:
        raise ValueError("x must be > 0")
    if x > Decimal(1) / Decimal(2):
        raise ValueError("x must be <= 1/2")
    if n_terms < 2:
        raise ValueError("n_terms must be >= 2")

    S = Decimal(0)
    x_pow = x
    for k in range(1, n_terms + 1):
        term = x_pow / Decimal(k)
        if k % 2 == 0:
            S -= term
        else:
            S += term
        x_pow *= x

    next_mag = x_pow / Decimal(n_terms + 1)

    if n_terms % 2 == 0:
        # S is a lower bound; upper bound is S + next_mag
        return S, S + next_mag
    else:
        # S is an upper bound; lower bound is S - next_mag
        return S - next_mag, S


def ln2_bounds(terms: int) -> Tuple[Decimal, Decimal]:
    """
    Certified bounds for ln(2) using:
      ln 2 = 2 * sum_{k>=0} u^{2k+1}/(2k+1) with u=1/3.
    Tail bounded by geometric series.
    """
    if terms < 1:
        raise ValueError("terms must be >= 1")
    u = Decimal(1) / Decimal(3)
    u2 = u * u
    S = Decimal(0)
    u_pow = u
    for k in range(terms):
        S += u_pow / Decimal(2 * k + 1)
        u_pow *= u2
    first_omitted = u_pow / Decimal(2 * terms + 1)
    rem = first_omitted / (Decimal(1) - u2)
    lb = Decimal(2) * S
    ub = Decimal(2) * (S + rem)
    return lb, ub


# ---------------------------
# Helper: stable Decimal ln/loglog for pivotA_proof
# ---------------------------

def dec_ln(x: Decimal) -> Decimal:
    """
    Deterministic high-precision ln for Decimal.
    If Decimal.ln() is unavailable, falls back to float (still deterministic).
    """
    if x <= 0:
        raise ValueError("ln argument must be > 0")
    if hasattr(x, "ln"):
        return x.ln()  # type: ignore[attr-defined]
    # fallback (less ideal, but deterministic)
    return Decimal(str(math.log(float(x))))


def dec_loglog(x: Decimal) -> Decimal:
    return dec_ln(dec_ln(x))


# ---------------------------
# mreq(y): exact certification via prefix sums + binary search (FAIL-fast)
# ---------------------------

@dataclass(frozen=True)
class MreqExactResult:
    y: int
    status: str               # "OK", "FAIL_PRIME_LIMIT", "FAIL_AMBIG"
    mreq: Optional[int]       # present iff status == "OK"


class MreqCertifier:
    """
    Precomputes per-prime certified bounds for ln(1 + 1/(p-1)) and prefix sums.

    For each y:
      idx = first prime >= y
      - if max UB tail <= ln2_lb => FAIL_PRIME_LIMIT
      - find smallest m with LB tail > ln2_ub (binary search)
      - minimality check: previous UB tail <= ln2_lb, else FAIL_AMBIG
    """

    def __init__(self, primes: List[int], *, prec: int, ln1p_terms: int, ln2_terms: int):
        if not primes or primes[-1] < 3:
            raise ValueError("Prime list too short (need primes >= 3).")

        getcontext().prec = prec
        self.primes = primes
        self.ln2_lb, self.ln2_ub = ln2_bounds(ln2_terms)

        n = len(primes)
        self._lb = [Decimal(0)] * n
        self._ub = [Decimal(0)] * n

        for i, p in enumerate(primes):
            if p < 3:
                continue
            x = Decimal(1) / Decimal(p - 1)  # <= 1/2 for p>=3
            lb, ub = ln1p_bounds_alt(x, ln1p_terms)
            self._lb[i] = lb
            self._ub[i] = ub

        self._pref_lb = [Decimal(0)] * (n + 1)
        self._pref_ub = [Decimal(0)] * (n + 1)
        for i in range(n):
            self._pref_lb[i + 1] = self._pref_lb[i] + self._lb[i]
            self._pref_ub[i + 1] = self._pref_ub[i] + self._ub[i]

    def _tail_lb(self, idx: int, m: int) -> Decimal:
        return self._pref_lb[idx + m] - self._pref_lb[idx]

    def _tail_ub(self, idx: int, m: int) -> Decimal:
        return self._pref_ub[idx + m] - self._pref_ub[idx]

    def mreq_exact(self, y: int) -> MreqExactResult:
        if y < 3:
            return MreqExactResult(y=y, status="FAIL_AMBIG", mreq=None)

        idx = bisect.bisect_left(self.primes, y)
        if idx >= len(self.primes):
            return MreqExactResult(y=y, status="FAIL_PRIME_LIMIT", mreq=None)

        max_tail_ub = self._pref_ub[-1] - self._pref_ub[idx]
        if max_tail_ub <= self.ln2_lb:
            return MreqExactResult(y=y, status="FAIL_PRIME_LIMIT", mreq=None)

        lo = 1
        hi = len(self.primes) - idx
        if self._tail_lb(idx, hi) <= self.ln2_ub:
            return MreqExactResult(y=y, status="FAIL_AMBIG", mreq=None)

        while lo < hi:
            mid = (lo + hi) // 2
            if self._tail_lb(idx, mid) > self.ln2_ub:
                hi = mid
            else:
                lo = mid + 1
        m = lo

        if m > 1:
            prev_ub = self._tail_ub(idx, m - 1)
            if prev_ub > self.ln2_lb:
                return MreqExactResult(y=y, status="FAIL_AMBIG", mreq=None)

        return MreqExactResult(y=y, status="OK", mreq=m)


# ---------------------------
# mreq(y): analytic lower bound (closed-form, for y>=Y0)
# ---------------------------

@dataclass(frozen=True)
class MreqResult:
    y: int
    status: str               # "OK_EXACT", "OK_ANALYTIC", or FAIL_*
    mreq: Optional[int]


def mreq_analytic_lower_bound(y: int, C1: float) -> int:
    # mreq(y) >= ceil(C1*y^2/log y)
    ly = math.log(y)
    if ly <= 0:
        raise ValueError("log y must be > 0")
    return int(math.ceil(C1 * (y * y) / ly))


def get_mreq(
    y: int,
    mreq_mode: str,
    cert: Optional[MreqCertifier],
    *,
    C1: float,
    Y0: int
) -> MreqResult:
    """
    mreq_mode:
      - "exact": exact certification only (may FAIL)
      - "analytic": analytic LB only, valid for y>=Y0 (else FAIL_BELOW_Y0)
      - "hybrid": try exact; if FAIL and y>=Y0 use analytic LB
    """
    if mreq_mode not in ("exact", "analytic", "hybrid"):
        raise ValueError("unknown mreq_mode")

    if mreq_mode in ("exact", "hybrid"):
        if cert is None:
            return MreqResult(y=y, status="FAIL_INTERNAL_NO_CERT", mreq=None)
        ex = cert.mreq_exact(y)
        if ex.status == "OK":
            return MreqResult(y=y, status="OK_EXACT", mreq=int(ex.mreq))  # type: ignore[arg-type]
        if mreq_mode == "exact":
            return MreqResult(y=y, status=ex.status, mreq=None)
        # hybrid fallback
        if y < Y0:
            return MreqResult(y=y, status=ex.status, mreq=None)
        # fall through to analytic

    # analytic
    if y < Y0:
        return MreqResult(y=y, status="FAIL_BELOW_Y0", mreq=None)
    return MreqResult(y=y, status="OK_ANALYTIC", mreq=mreq_analytic_lower_bound(y, C1))


# ---------------------------
# h(y) models
# ---------------------------

def h_of_y(y: int, mode: str, H: float, alpha: float, beta: float) -> float:
    if mode == "const":
        return float(H)
    if mode == "power":
        return float(math.exp(alpha * math.log(y)))  # y^alpha
    if mode == "logpower":
        ly = math.log(y)
        if ly <= 0:
            return 1.0
        return float(math.exp(beta * math.log(ly)))  # (log y)^beta
    raise ValueError("Unknown h_mode")


# ---------------------------
# Closed cap models: logN(y)
# ---------------------------

def logN_of_y(y: int, model: str, c: float, A: float) -> float:
    if y < 3:
        raise ValueError("y must be >= 3")
    ly = math.log(y)

    if model == "exp_y2":
        return c * (y * y)
    if model == "y_pow_ay":
        return A * y * ly
    if model == "exp_y2_over_log":
        return c * (y * y) / ly

    raise ValueError("Unknown Ny_model")


def load_logN_table(path: str) -> Dict[int, float]:
    out: Dict[int, float] = {}
    with open(path, "r", newline="", encoding="utf-8") as f:
        r = csv.DictReader(f)
        if not r.fieldnames or "y" not in r.fieldnames or "logN" not in r.fieldnames:
            raise ValueError("CSV must have headers: y,logN")
        for row in r:
            yy = int(row["y"])
            logN = float(row["logN"])
            out[yy] = logN
    return out


# ---------------------------
# Derived quantities (legacy)
# ---------------------------

def wy_from_logN(y: int, logN: float) -> int:
    return int(math.floor(logN / math.log(y)))


def delta_value(y: int, logN: float, eps: float, hy: float) -> float:
    return (eps * math.log(y) - math.log(hy)) / logN


def kmax_from_delta(delta: float) -> int:
    return int(math.ceil(1.0 / delta))


# ---------------------------
# Tables + hashing
# ---------------------------

@dataclass(frozen=True)
class Row:
    y: int
    mreq_status: str          # OK_EXACT / OK_ANALYTIC / FAIL_*
    mreq: str                 # integer as string or "-"
    logN: float
    Wy: int
    h: float
    delta: float
    Kmax: str
    M: str
    verdict: str              # YES / NO / FAIL_*


@dataclass(frozen=True)
class PivotRow:
    y: int
    mreq_status: str
    mreq: str


def sha256_text(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def render_table(cols: List[str], rows: List[List[str]], title: Optional[str] = None) -> str:
    w = [len(c) for c in cols]
    for r in rows:
        for i, v in enumerate(r):
            w[i] = max(w[i], len(v))

    def sep() -> str:
        return "+" + "+".join("-" * (wi + 2) for wi in w) + "+\n"

    def line(vals: List[str]) -> str:
        return "|" + "|".join(" " + v.ljust(wi) + " " for v, wi in zip(vals, w)) + "|\n"

    out = ""
    if title:
        out += title.rstrip() + "\n"
    out += sep()
    out += line(cols)
    out += sep()
    for r in rows:
        out += line(r)
    out += sep()
    return out


def stable_Y1_from_rows(rows: List[Row]) -> Optional[int]:
    ok_suffix = True
    stable = None
    for r in reversed(rows):
        ok_suffix = ok_suffix and (r.verdict == "YES")
        if ok_suffix:
            stable = r.y
    return stable


# ---------------------------
# Appendix A constants report (Mertens + nth prime) + hash
# ---------------------------

def pivotA_constants_report(
    mertens_ref: str,
    mertens_x0: int,
    mertens_B1: float,
    mertens_c: float,
    nthprime_ref: str,
    nthprime_n0: int,
) -> str:
    """
    Human-traceable constants for Appendix A.

    Expected explicit published inequality (two-sided):
        | sum_{p<=x} 1/p - (log log x + B1) | <= c/log x    for all x >= x0.

    Also record a published nth-prime bound domain:
        p_n <= n (log n + log log n)  for all n >= n0.
    """
    if mertens_x0 < 3:
        raise ValueError("--mertens_x0 must be >= 3")
    if nthprime_n0 < 1:
        raise ValueError("--nthprime_n0 must be >= 1")
    if mertens_c < 0:
        raise ValueError("--mertens_c must be >= 0")

    cols = ["constant", "value"]
    rows = [
        ["Mertens reference", mertens_ref],
        ["x0 (validity threshold)", str(mertens_x0)],
        ["B1 (Meissel–Mertens-type constant used in bound)", f"{mertens_B1:.12f}"],
        ["c (error coefficient in c/log x)", f"{mertens_c:.6g}"],
        ["Assumed bound", f"|sum_{{p<=x}} 1/p - (log log x + B1)| <= c/log x   (x >= x0)"],
        ["nth-prime reference", nthprime_ref],
        ["n0 (validity threshold)", str(nthprime_n0)],
        ["nth-prime bound", "p_n <= n (log n + log log n)  (n >= n0)"],
    ]
    txt = render_table(cols, rows, title="Appendix A — Traceable constants")
    txt += "sha256=" + sha256_text(txt) + "\n"
    return txt


# ---------------------------
# Appendix A proof endpoint check (Step 4) + hash
# ---------------------------

def pivotA_proof_report(
    *,
    C1: float,
    Y0: int,
    mertens_ref: str,
    mertens_x0: int,
    mertens_B1: float,
    mertens_c: float,
    nthprime_ref: str,
    nthprime_n0: int,
    prec: int,
    ln2_terms: int,
) -> str:
    """
    Endpoint check for the corrected Step 4 logic:

    Let y=Y0, m=floor(C1*y^2/log y), n=m+y-1.
    Using nth-prime bound: p_n <= n(ln n + ln ln n) => x_upper.
    Using two-sided Mertens-type bound:
        sum_{y<=p<=x} 1/p <= (loglog x - loglog y) + c/log x + c/log y
    and squares bound: <= 1/(y-1).

    Thus:
        log UB_m(y) <= (loglog x_upper - loglog y) + c/log x_upper + c/log y + 1/(y-1).
    We check RHS_upper < ln 2.

    IMPORTANT: this fixes your earlier failure: discarding -sum_{p<y}1/p makes the bound useless.
    """
    if Y0 < 3:
        raise ValueError("--Y0 must be >= 3")
    if C1 <= 0:
        raise ValueError("--C1 must be > 0")
    if mertens_x0 < 3:
        raise ValueError("--mertens_x0 must be >= 3")
    if nthprime_n0 < 1:
        raise ValueError("--nthprime_n0 must be >= 1")

    getcontext().prec = prec
    y = int(Y0)

    ln2_lb, ln2_ub = ln2_bounds(ln2_terms)
    dy = Decimal(y)

    ln_y = dec_ln(dy)
    m = int((Decimal(str(C1)) * dy * dy / ln_y).to_integral_value(rounding="ROUND_FLOOR"))
    if m < 1:
        m = 1
    n = m + y - 1

    # nth-prime bound applicability
    nth_ok = (n >= nthprime_n0)

    dn = Decimal(n)
    ln_n = dec_ln(dn)
    lnln_n = dec_ln(ln_n)

    # x_upper := n*(ln n + ln ln n)
    x_upper = dn * (ln_n + lnln_n)

    # Mertens applicability: need y>=x0 and x_upper>=x0 (and in the proof x>=y, so ok)
    mert_ok = (y >= mertens_x0) and (x_upper >= Decimal(mertens_x0))

    loglog_x = dec_loglog(x_upper)
    loglog_y = dec_loglog(dy)

    # RHS_upper := (loglog x - loglog y) + c/log x + c/log y + 1/(y-1)
    cD = Decimal(str(mertens_c))
    rhs = (loglog_x - loglog_y) + (cD / dec_ln(x_upper)) + (cD / ln_y) + (Decimal(1) / Decimal(y - 1))

    ok = (rhs < ln2_lb)

    cols = ["item", "value"]
    rows = [
        ["C1", f"{C1}"],
        ["Y0", f"{Y0}"],
        ["y", str(y)],
        ["m := floor(C1*y^2/log y)", str(m)],
        ["n := m+y-1", str(n)],
        ["nth-prime bound used?", "YES" if nth_ok else "NO"],
        ["Mertens reference", mertens_ref],
        ["Mertens x0", str(mertens_x0)],
        ["Mertens B1", f"{mertens_B1}"],
        ["Mertens c", f"{mertens_c}"],
        ["Mertens bound usable at endpoint?", "YES" if mert_ok else "NO"],
        ["nth-prime reference", nthprime_ref],
        ["nth-prime n0", str(nthprime_n0)],
        ["Decimal prec", str(prec)],
        ["ln2_terms", str(ln2_terms)],
        ["ln2 interval", f"[{ln2_lb}, {ln2_ub}]"],
        ["x_upper := n*(ln n + ln ln n)", f"{x_upper}"],
        ["loglog(x_upper)", f"{loglog_x}"],
        ["loglog(y)", f"{loglog_y}"],
        ["c/log x_upper", f"{(cD / dec_ln(x_upper))}"],
        ["c/log y", f"{(cD / ln_y)}"],
        ["1/(y-1)", f"{(Decimal(1)/Decimal(y-1))}"],
        ["RHS_upper", f"{rhs}"],
        ["Certified RHS_upper < ln2_lb ?", "YES" if ok else "NO"],
    ]

    txt = render_table(cols, rows, title="Appendix A — pivotA_proof endpoint check (correct Step 3/4 logic)")
    txt += "sha256=" + sha256_text(txt) + "\n"
    return txt


# ---------------------------
# Main
# ---------------------------

def main() -> None:
    ap = argparse.ArgumentParser(
        description=(
            "Compute mreq(y) (exact certified or analytic closed-form) and compare against upper bound M(y)=Wy+Kmax.\n"
            "FAIL-fast: insufficient resources yield FAIL_* rows (no crash)."
        )
    )

    ap.add_argument(
        "--mode",
        choices=["window", "caseB", "pivotA", "pivot_only", "pivotA_proof"],
        default="caseB",
        help=(
            "window: legacy full table + first-hit Y1; "
            "caseB: legacy full table + stable suffix-Y1; "
            "pivotA: print Appendix A constants (Mertens+nth prime) + sha256; "
            "pivot_only: print pivot-only table (y,mreq) + sha256; "
            "pivotA_proof: Appendix A endpoint proof check (Step 4) + sha256."
        ),
    )

    ap.add_argument("--y_min", type=int, default=3)
    ap.add_argument("--y_max", type=int, default=200)
    ap.add_argument("--prime_limit", type=int, default=1_000_000)

    # cap (legacy / other appendices)
    cap = ap.add_mutually_exclusive_group(required=False)
    cap.add_argument("--Ny", type=int, default=None, help="Legacy fixed window cap Ny (integer).")
    cap.add_argument("--Ny_model", choices=["exp_y2", "y_pow_ay", "exp_y2_over_log"], default="exp_y2",
                     help="Closed-form model for N(y). Ignored if --Ny is provided.")
    ap.add_argument("--c", type=float, default=1e-4, help="Constant c used by exp_* models.")
    ap.add_argument("--A", type=float, default=2.0, help="Constant A used by y_pow_ay model.")
    ap.add_argument("--Ny_table", type=str, default=None,
                    help="Optional CSV mapping y->logN (headers: y,logN). Overrides --Ny_model for listed y.")

    ap.add_argument("--eps", type=float, default=0.08)

    # mreq model
    ap.add_argument("--mreq_mode", choices=["exact", "analytic", "hybrid"], default="exact",
                    help="exact: certified by prime list; analytic: closed-form LB valid for y>=Y0; hybrid: exact then analytic fallback.")
    ap.add_argument("--C1", type=float, default=1e-3, help="Analytic LB constant: mreq(y) >= ceil(C1*y^2/log y) for y>=Y0.")
    ap.add_argument("--Y0", type=int, default=30000, help="Validity threshold for analytic mreq lower bound / Appendix A endpoint y.")

    # Certification controls (exact mreq mode)
    ap.add_argument("--prec", type=int, default=120)
    ap.add_argument("--ln1p_terms", type=int, default=18)
    ap.add_argument("--ln2_terms", type=int, default=40)

    # h(y)
    ap.add_argument("--h_mode", choices=["const", "power", "logpower"], default="const")
    ap.add_argument("--H", type=float, default=64.0)
    ap.add_argument("--alpha", type=float, default=0.04)
    ap.add_argument("--beta", type=float, default=3.0)

    # Appendix A constants (traceability)
    ap.add_argument("--mertens_ref", type=str, default="(FILL ME) explicit published Mertens-type inequality",
                    help="Reference string for the chosen explicit Mertens bound used in Appendix A.")
    ap.add_argument("--mertens_x0", type=int, default=55,
                    help="Validity threshold x0 for the chosen Mertens-type inequality.")
    ap.add_argument("--mertens_B1", type=float, default=0.2614972128,
                    help="Constant B1 in the two-sided bound around log log x + B1.")
    ap.add_argument("--mertens_c", type=float, default=1.0,
                    help="Error coefficient c in the two-sided bound: |...| <= c/log x.")
    ap.add_argument("--nthprime_ref", type=str, default="(FILL ME) explicit published nth-prime upper bound",
                    help="Reference string for the chosen explicit nth-prime upper bound.")
    ap.add_argument("--nthprime_n0", type=int, default=6,
                    help="Validity threshold n0 for p_n <= n(log n + log log n).")

    # Optional CSV dump (legacy full modes)
    ap.add_argument("--out_csv", type=str, default=None,
                    help="Optional: write the produced table to CSV (full modes only).")
    ap.add_argument("--hash_csv", action="store_true",
                    help="If set and --out_csv is used, also print sha256 of the CSV content.")

    args = ap.parse_args()

    # modes: pivotA / pivotA_proof (no sieve needed)
    if args.mode == "pivotA":
        print(pivotA_constants_report(
            mertens_ref=args.mertens_ref,
            mertens_x0=args.mertens_x0,
            mertens_B1=args.mertens_B1,
            mertens_c=args.mertens_c,
            nthprime_ref=args.nthprime_ref,
            nthprime_n0=args.nthprime_n0,
        ), end="")
        return

    if args.mode == "pivotA_proof":
        print(pivotA_proof_report(
            C1=args.C1,
            Y0=args.Y0,
            mertens_ref=args.mertens_ref,
            mertens_x0=args.mertens_x0,
            mertens_B1=args.mertens_B1,
            mertens_c=args.mertens_c,
            nthprime_ref=args.nthprime_ref,
            nthprime_n0=args.nthprime_n0,
            prec=args.prec,
            ln2_terms=args.ln2_terms,
        ), end="")
        return

    # We always need a prime list at least up to y_max to iterate over y primes.
    prime_limit = max(args.prime_limit, args.y_max + 100)
    primes = sieve_primes(prime_limit)
    if not primes or primes[-1] < 3:
        raise ValueError("prime_limit too small (need primes >= 3).")

    # Precompute certifier only if needed
    cert: Optional[MreqCertifier] = None
    if args.mreq_mode in ("exact", "hybrid"):
        cert = MreqCertifier(
            primes,
            prec=args.prec,
            ln1p_terms=args.ln1p_terms,
            ln2_terms=args.ln2_terms,
        )

    ys = [p for p in primes if p >= 3 and args.y_min <= p <= args.y_max]

    # mode pivot_only: pivot table + sha256
    if args.mode == "pivot_only":
        prows: List[PivotRow] = []
        for y in ys:
            mr_res = get_mreq(y, args.mreq_mode, cert, C1=args.C1, Y0=args.Y0)
            if mr_res.mreq is None:
                prows.append(PivotRow(y=y, mreq_status=mr_res.status, mreq="-"))
            else:
                prows.append(PivotRow(y=y, mreq_status=mr_res.status, mreq=str(int(mr_res.mreq))))

        cols = ["y", "mreq_status", "mreq(y)"]
        rows2 = [[str(r.y), r.mreq_status, r.mreq] for r in prows]
        title = (
            "Pivot-only table (Appendix A)\n"
            f"mreq_mode={args.mreq_mode}  (prec={args.prec}, ln1p_terms={args.ln1p_terms}, ln2_terms={args.ln2_terms})\n"
            f"y in [{args.y_min},{args.y_max}], prime_limit={prime_limit}"
        )
        txt = render_table(cols, rows2, title=title)
        txt += "sha256=" + sha256_text(txt) + "\n"
        print(txt, end="")
        return

    # Legacy / full modes below
    logN_table: Dict[int, float] = {}
    if args.Ny_table is not None:
        logN_table = load_logN_table(args.Ny_table)

    rows_full: List[Row] = []
    cap_desc = ""

    for y in ys:
        mr_res = get_mreq(y, args.mreq_mode, cert, C1=args.C1, Y0=args.Y0)

        # Determine logN(y)
        if args.Ny is not None:
            if args.Ny <= 1:
                raise ValueError("--Ny must be >= 2")
            logN = math.log(args.Ny)
            cap_desc = f"Ny={args.Ny}"
        else:
            if y in logN_table:
                logN = logN_table[y]
            else:
                logN = logN_of_y(y, args.Ny_model, args.c, args.A)
            cap_desc = f"N(y) via {args.Ny_model} (c={args.c}, A={args.A})"
            if args.Ny_table:
                cap_desc += f", table override={args.Ny_table}"

        if logN <= 0:
            raise ValueError(f"logN(y) must be > 0, got {logN} at y={y}")

        Wy = wy_from_logN(y, logN)
        hy = h_of_y(y, args.h_mode, args.H, args.alpha, args.beta)
        d = delta_value(y, logN, args.eps, hy)

        # If mreq not available => verdict FAIL_*
        if mr_res.mreq is None:
            rows_full.append(
                Row(
                    y=y,
                    mreq_status=mr_res.status,
                    mreq="-",
                    logN=logN,
                    Wy=Wy,
                    h=hy,
                    delta=d,
                    Kmax="-",
                    M="-",
                    verdict=mr_res.status,
                )
            )
            continue

        mr = int(mr_res.mreq)

        # If delta <= 0, cannot form Kmax/M in this model
        if d <= 0:
            rows_full.append(
                Row(
                    y=y,
                    mreq_status=mr_res.status,
                    mreq=str(mr),
                    logN=logN,
                    Wy=Wy,
                    h=hy,
                    delta=d,
                    Kmax="-",
                    M="-",
                    verdict="NO",
                )
            )
            continue

        Kint = kmax_from_delta(d)
        Mval = Wy + Kint
        verdict = "YES" if Mval < mr else "NO"

        rows_full.append(
            Row(
                y=y,
                mreq_status=mr_res.status,
                mreq=str(mr),
                logN=logN,
                Wy=Wy,
                h=hy,
                delta=d,
                Kmax=str(Kint),
                M=str(Mval),
                verdict=verdict,
            )
        )

    # Render full table
    cols = ["y", "mreq_status", "mreq(y)", "logN(y)", "Wy", "h(y)", "delta", "Kmax", "M=Wy+Kmax", "verdict"]
    rows2 = []
    for r in rows_full:
        rows2.append(
            [
                str(r.y),
                r.mreq_status,
                r.mreq,
                f"{r.logN:.6g}",
                str(r.Wy),
                f"{r.h:.6g}",
                f"{r.delta:.6g}",
                r.Kmax,
                r.M,
                r.verdict,
            ]
        )

    title = (
        f"Case B scan under cap {cap_desc}, eps={args.eps}\n"
        f"h_mode={args.h_mode}, H={args.H}, alpha={args.alpha}, beta={args.beta}\n"
        f"mreq_mode={args.mreq_mode} (C1={args.C1}, Y0={args.Y0})\n"
        f"y in [{args.y_min},{args.y_max}], prime_limit={prime_limit}"
    )
    txt = render_table(cols, rows2, title=title)
    print(txt, end="")

    # Optional CSV dump (Appendix tables / traceability)
    if args.out_csv is not None:
        with open(args.out_csv, "w", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerow(cols)
            for r in rows2:
                w.writerow(r)
        if args.hash_csv:
            with open(args.out_csv, "rb") as f:
                h = hashlib.sha256(f.read()).hexdigest()
            print(f"csv_path={args.out_csv}")
            print(f"csv_sha256={h}")

    # Legacy summaries
    if args.mode == "window":
        Y1_first = None
        for r in rows_full:
            if r.verdict == "YES":
                Y1_first = r.y
                break
        if Y1_first is None:
            print("Y1 (first-hit): not found on this scanned y-range.")
        else:
            print(f"Y1 (first-hit): y={Y1_first} on this scanned y-range.")
        return

    # args.mode == "caseB"
    Y1_stable = stable_Y1_from_rows(rows_full)
    if Y1_stable is None:
        print("Y1 (stable): not found as a stable suffix on this scanned y-range.")
        print("Note: any FAIL_* rows or NO rows in the tail block stability.")
    else:
        print(f"Y1 (stable): y={Y1_stable} on this scanned y-range.")


if __name__ == "__main__":
    main()
