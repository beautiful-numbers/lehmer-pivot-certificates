#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
appendixB_fast_candidates.py

FAST (cheap, non-normative) candidate generator for Appendix B.

Purpose:
  For each prime y in [3, Ymax), find a candidate minimal window end j such that
      sum_{k=i..j-1} log(p_k/(p_k-1)) > log(2)
  where y = primes[i] and p_k are consecutive primes.

Outputs (TSV by default, PowerShell-friendly):
  y    m    p_m1    p_m    STATUS    gap_log

Where:
  m = j - i
  p_m  = primes[j-1]
  p_m1 = primes[j-2] if m>=2 else 1
  gap_log = (prefix[j]-prefix[i]) - log(2)  (float, just diagnostic)

STATUS:
  OK        : candidate found under prime_cap
  FAIL_CAP  : ran out of primes under prime_cap before crossing log(2)

Important:
  - This script is NOT normative. It produces candidates only.
  - Certification is done by the REFINE script (normative, integer-only comparisons).

Usage examples:
  # candidates for y < 2000 (recommended for your Y1=2000 workflow)
  python appendixB_fast_candidates.py --ymax 2000 --prime_cap 5000000 --format tsv > out/cheap_table.tsv

  # candidates for y < 30000 (only if prime_cap is sufficient for your machine / method)
  python appendixB_fast_candidates.py --ymax 30000 --prime_cap 20000000 --format tsv > out/cheap_table.tsv
"""

from __future__ import annotations

import argparse
import math
from math import isqrt
from typing import List


# ============================================================
# Sieve + helpers
# ============================================================

def sieve_primes_upto(n: int) -> List[int]:
    """Bytearray sieve primes <= n (inclusive)."""
    if n < 2:
        return []
    bs = bytearray(b"\x01") * (n + 1)
    bs[0:2] = b"\x00\x00"
    # strike evens > 2
    bs[4:n+1:2] = b"\x00" * (((n - 4) // 2) + 1)
    r = isqrt(n)
    p = 3
    while p <= r:
        if bs[p]:
            step = 2 * p
            start = p * p
            bs[start:n+1:step] = b"\x00" * (((n - start) // step) + 1)
        p += 2
    return [2] + [i for i in range(3, n + 1, 2) if bs[i]]


def lower_bound(arr: List[int], x: int) -> int:
    """First index i with arr[i] >= x (arr sorted)."""
    lo, hi = 0, len(arr)
    while lo < hi:
        mid = (lo + hi) // 2
        if arr[mid] < x:
            lo = mid + 1
        else:
            hi = mid
    return lo


# ============================================================
# Prefix logs + two-pointers
# ============================================================

def build_prefix_logs(primes: List[int]) -> List[float]:
    """
    prefix[k] = sum_{t<k} log(p_t/(p_t-1)).
    prefix length = len(primes)+1.
    """
    pref = [0.0] * (len(primes) + 1)
    s = 0.0
    for i, p in enumerate(primes, start=1):
        # p=2 contributes log(2) but y>=3 anyway; keep it for simplicity
        s += math.log(p / (p - 1.0))
        pref[i] = s
    return pref


def find_min_j_crossing(pref: List[float], i: int, j0: int, log2: float) -> int:
    """
    Find minimal j >= max(j0, i+1) such that pref[j] - pref[i] > log2.
    Returns j = len(pref) if not found (i.e., ran out).
    """
    j = max(j0, i + 1)
    n = len(pref) - 1
    while j <= n and (pref[j] - pref[i]) <= log2:
        j += 1
    return j


# ============================================================
# Output
# ============================================================

def print_header(fmt: str) -> None:
    if fmt == "tsv":
        print("y\tm\tp_m1\tp_m\tSTATUS\tgap_log")
    else:
        print(r"% y & m & p_{m-1} & p_m & STATUS & gap\_log \\")


def print_row(fmt: str, y: int, m: int, p_m1: int, p_m: int, status: str, gap_log: float) -> None:
    if fmt == "tsv":
        if math.isnan(gap_log):
            g = "nan"
        else:
            g = f"{gap_log:.6e}"
        print(f"{y}\t{m}\t{p_m1}\t{p_m}\t{status}\t{g}")
    else:
        # TeX row (no tabular env)
        g = "nan" if math.isnan(gap_log) else f"{gap_log:.2e}"
        print(f"{y} & {m} & {p_m1} & {p_m} & \\texttt{{{status}}} & {g} \\\\")


# ============================================================
# Main
# ============================================================

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ymax", type=int, default=2000,
                    help="Generate candidates for primes y with 3 <= y < ymax.")
    ap.add_argument("--prime_cap", type=int, default=5_000_000,
                    help="Sieve primes up to this cap (inclusive).")
    ap.add_argument("--format", choices=["tsv", "tex"], default="tsv")
    ap.add_argument("--verbose_every", type=int, default=200,
                    help="Progress message every N y's (0 disables).")
    args = ap.parse_args()

    if args.ymax <= 3:
        raise SystemExit("Need --ymax > 3")

    print(f"[sieve] sieving primes up to {args.prime_cap} ...", flush=True)
    primes = sieve_primes_upto(args.prime_cap)
    if not primes or primes[-1] < args.ymax:
        raise SystemExit("prime_cap too small: max prime below ymax; increase --prime_cap")

    pref = build_prefix_logs(primes)
    log2 = math.log(2.0)

    i0 = lower_bound(primes, 3)
    i_end = lower_bound(primes, args.ymax)
    total = max(0, i_end - i0)
    if total == 0:
        raise SystemExit("No primes in [3, ymax).")

    print_header(args.format)

    j0 = i0 + 1
    for t, i in enumerate(range(i0, i_end), start=1):
        y = primes[i]

        j = find_min_j_crossing(pref, i, j0, log2)
        if j > len(primes):
            # safety (shouldn't happen)
            j = len(primes) + 1

        if j >= len(pref):
            # FAIL_CAP (ran out under current prime_cap)
            print_row(args.format, y=y, m=-1, p_m1=1, p_m=1, status="FAIL_CAP", gap_log=float("nan"))
            continue

        # Candidate window [i, j)
        j0 = max(j0, j)
        m = j - i
        p_m = primes[j - 1]
        p_m1 = primes[j - 2] if m >= 2 else 1
        gap = (pref[j] - pref[i]) - log2  # should be > 0 in exact arithmetic

        print_row(args.format, y=y, m=m, p_m1=p_m1, p_m=p_m, status="OK", gap_log=gap)

        if args.verbose_every and (t == 1 or t % args.verbose_every == 0 or t == total):
            print(f"[{t}/{total}] y={y} m={m} p_m={p_m} (prime_max={primes[-1]})", flush=True)

if __name__ == "__main__":
    main()
