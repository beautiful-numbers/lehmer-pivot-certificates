#!/usr/bin/env python3
# -*- coding: utf-8 -*-

r"""
appendixB_refine_certify_bounds.py

Referee/OPN-style: certify m_req(y) on a finite small range 3<=y<Y1
using ONLY finite integer arithmetic on explicit rational grids.

We certify:
  UB_{m-1}(y) <= 2 < UB_m(y)
via certified log bounds on UB.

For the paper, the preferred TeX output is a compact human-readable table with columns
  y, m, p_{y,m-1}, p_{y,m}, g_-, g_+
where
  g_- = L_lo_num - UP(i,j-1)   >= 0
  g_+ = LO(i,j)   - L_hi_num   > 0
and L_lo_num, L_hi_num are the integer enclosure endpoints of log(2)
over the common denominator DEN.

This script is NOT part of the proof; the proof uses only the finite table it prints.
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from math import isqrt, gcd
from typing import Dict, List, Optional


# ------------------------
# UTF robustness
# ------------------------
def _detect_encoding(path: str) -> str:
    with open(path, "rb") as fb:
        head = fb.read(4)
    if head.startswith(b"\xff\xfe") or head.startswith(b"\xfe\xff"):
        return "utf-16"
    if head.startswith(b"\xef\xbb\xbf"):
        return "utf-8-sig"
    return "utf-8"


# =========================
# Sieve primes
# =========================
def sieve_primes_upto(n: int) -> List[int]:
    if n < 2:
        return []
    bs = bytearray(b"\x01") * (n + 1)
    bs[0:2] = b"\x00\x00"
    bs[4:n + 1:2] = b"\x00" * (((n - 4) // 2) + 1)
    r = isqrt(n)
    p = 3
    while p <= r:
        if bs[p]:
            step = 2 * p
            start = p * p
            bs[start:n + 1:step] = b"\x00" * (((n - start) // step) + 1)
        p += 2
    return [2] + [i for i in range(3, n + 1, 2) if bs[i]]


# =========================
# Fractions a/b
# =========================
@dataclass(frozen=True)
class Frac:
    a: int
    b: int

    @staticmethod
    def parse(s: str) -> "Frac":
        s = s.strip()
        if "/" not in s:
            raise ValueError("Need a/b")
        x, y = s.split("/", 1)
        a, b = int(x), int(y)
        if b == 0:
            raise ValueError("Denominator 0")
        if b < 0:
            a, b = -a, -b
        g = gcd(abs(a), b)
        return Frac(a // g, b // g)


# =========================
# Cheap TSV parsing
# Expected: y \t m \t p_m1 \t p_m \t ...
# We only require y and p_m.
# =========================
@dataclass
class CheapRow:
    y: int
    m_in: Optional[int]
    p_m1_in: Optional[int]
    p_m_in: Optional[int]


def _looks_like_int(tok: str) -> bool:
    tok = tok.strip().lstrip("\ufeff")
    if tok.startswith(("+", "-")):
        tok = tok[1:]
    return tok.isdigit()


def _int_or_none(tok: str) -> Optional[int]:
    t = tok.strip()
    if t == "" or t == "-" or t.lower() == "nan":
        return None
    try:
        return int(t)
    except Exception:
        return None


def read_cheap_tsv(path: str) -> Dict[int, CheapRow]:
    enc = _detect_encoding(path)
    out: Dict[int, CheapRow] = {}
    with open(path, "r", encoding=enc, errors="strict") as f:
        for raw in f:
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split("\t")
            if not parts:
                continue
            if not _looks_like_int(parts[0]):
                continue
            y = int(parts[0].lstrip("\ufeff"))
            m_in = _int_or_none(parts[1]) if len(parts) > 1 else None
            p_m1_in = _int_or_none(parts[2]) if len(parts) > 2 else None
            p_m_in = _int_or_none(parts[3]) if len(parts) > 3 else None
            out[y] = CheapRow(y=y, m_in=m_in, p_m1_in=p_m1_in, p_m_in=p_m_in)
    return out


# =========================
# Integer helpers
# =========================
def div_floor(a: int, b: int) -> int:
    return a // b


def div_ceil(a: int, b: int) -> int:
    return (a + b - 1) // b


# =========================
# Prefix sums
# =========================
@dataclass
class PrefixPack:
    primes: List[int]
    idx: Dict[int, int]
    S: int
    D: int
    DEN: int  # 60*S

    puU: List[int]
    pu2L: List[int]
    pu3U: List[int]
    pu4L: List[int]
    pu5U: List[int]

    puL: List[int]
    pu2U: List[int]
    pu3L: List[int]
    pu4U: List[int]


def build_prefixes(primes: List[int], D: int) -> PrefixPack:
    S = 10 ** D
    DEN = 60 * S
    idx = {p: i for i, p in enumerate(primes)}

    puU = [0]
    pu2L = [0]
    pu3U = [0]
    pu4L = [0]
    pu5U = [0]

    puL = [0]
    pu2U = [0]
    pu3L = [0]
    pu4U = [0]

    for p in primes:
        if p < 3:
            puU.append(puU[-1])
            pu2L.append(pu2L[-1])
            pu3U.append(pu3U[-1])
            pu4L.append(pu4L[-1])
            pu5U.append(pu5U[-1])

            puL.append(puL[-1])
            pu2U.append(pu2U[-1])
            pu3L.append(pu3L[-1])
            pu4U.append(pu4U[-1])
            continue

        q = p - 1
        q2 = q * q
        q3 = q2 * q
        q4 = q2 * q2
        q5 = q4 * q

        uU = div_ceil(S, q)
        uL = div_floor(S, q)

        u2U = div_ceil(S, q2)
        u2L = div_floor(S, q2)

        u3U = div_ceil(S, q3)
        u3L = div_floor(S, q3)

        u4U = div_ceil(S, q4)
        u4L = div_floor(S, q4)

        u5U = div_ceil(S, q5)

        puU.append(puU[-1] + uU)
        pu2L.append(pu2L[-1] + u2L)
        pu3U.append(pu3U[-1] + u3U)
        pu4L.append(pu4L[-1] + u4L)
        pu5U.append(pu5U[-1] + u5U)

        puL.append(puL[-1] + uL)
        pu2U.append(pu2U[-1] + u2U)
        pu3L.append(pu3L[-1] + u3L)
        pu4U.append(pu4U[-1] + u4U)

    return PrefixPack(
        primes=primes, idx=idx, S=S, D=D, DEN=DEN,
        puU=puU, pu2L=pu2L, pu3U=pu3U, pu4L=pu4L, pu5U=pu5U,
        puL=puL, pu2U=pu2U, pu3L=pu3L, pu4U=pu4U
    )


def _sum(pref: List[int], i: int, j: int) -> int:
    return pref[j] - pref[i]


# =========================
# Bounds for log UB on window [i,j)
# =========================
def UP(pack: PrefixPack, i: int, j: int) -> int:
    suU = _sum(pack.puU, i, j)
    su2L = _sum(pack.pu2L, i, j)
    su3U = _sum(pack.pu3U, i, j)
    su4L = _sum(pack.pu4L, i, j)
    su5U = _sum(pack.pu5U, i, j)
    return 60 * suU - 30 * su2L + 20 * su3U - 15 * su4L + 12 * su5U


def LO(pack: PrefixPack, i: int, j: int) -> int:
    suL = _sum(pack.puL, i, j)
    su2U = _sum(pack.pu2U, i, j)
    su3L = _sum(pack.pu3L, i, j)
    su4U = _sum(pack.pu4U, i, j)
    return 60 * suL - 30 * su2U + 20 * su3L - 15 * su4U


# =========================
# Cross-multiplication comparisons
# =========================
def leq_frac(X_num: int, DEN: int, F: Frac) -> bool:
    return X_num * F.b <= F.a * DEN


def gt_frac(X_num: int, DEN: int, F: Frac) -> bool:
    return X_num * F.b > F.a * DEN


# =========================
# Convert rational enclosure endpoints to integer enclosure over DEN
# If L_lo <= log 2 <= L_hi, define:
#   L_lo_num = floor(DEN * L_lo)
#   L_hi_num = ceil (DEN * L_hi)
# Then:
#   L_lo_num / DEN <= L_lo <= log 2 <= L_hi <= L_hi_num / DEN
# =========================
def frac_floor_to_DEN(F: Frac, DEN: int) -> int:
    return (F.a * DEN) // F.b


def frac_ceil_to_DEN(F: Frac, DEN: int) -> int:
    return (F.a * DEN + F.b - 1) // F.b


# =========================
# Certification
# =========================
@dataclass
class OutRow:
    y: int
    m: int
    p_m1: int
    p_m: int
    status: str
    note: str
    UPm1: int
    LOm: int
    g_minus: int
    g_plus: int


def certify_one(
    pack: PrefixPack,
    y: int,
    p_m_cand: int,
    L_lo: Frac,
    L_hi: Frac,
    L_lo_num: int,
    L_hi_num: int,
    max_adjust: int
) -> OutRow:
    if y not in pack.idx:
        return OutRow(y, -1, 1, p_m_cand, "FAIL_Y", "y not in prime list", 0, 0, 0, 0)
    if p_m_cand not in pack.idx:
        return OutRow(y, -1, 1, p_m_cand, "FAIL_PM", "p_m not in prime list (cap too small?)", 0, 0, 0, 0)

    i = pack.idx[y]
    j = pack.idx[p_m_cand] + 1
    if j <= i:
        return OutRow(y, -1, 1, p_m_cand, "FAIL_ORDER", "p_m < y", 0, 0, 0, 0)

    adj = 0
    while not gt_frac(LO(pack, i, j), pack.DEN, L_hi):
        j += 1
        adj += 1
        if j > len(pack.primes) or adj > max_adjust:
            return OutRow(y, -1, 1, p_m_cand, "FAIL_CAP", "cannot reach LO > L_hi under cap/adjust", 0, 0, 0, 0)

    while True:
        UPm1 = UP(pack, i, j - 1)
        if leq_frac(UPm1, pack.DEN, L_lo):
            break

        if j - 1 <= i:
            return OutRow(y, -1, 1, p_m_cand, "FAIL_UP", "cannot make UP_{m-1} <= L_lo", UPm1, LO(pack, i, j), 0, 0)

        j_try = j - 1
        if gt_frac(LO(pack, i, j_try), pack.DEN, L_hi):
            j = j_try
            continue

        return OutRow(y, -1, 1, p_m_cand, "FAIL_UP", "UP_{m-1} > L_lo", UPm1, LO(pack, i, j), 0, 0)

    while j - 1 > i:
        j_try = j - 1
        if gt_frac(LO(pack, i, j_try), pack.DEN, L_hi) and leq_frac(UP(pack, i, j_try - 1), pack.DEN, L_lo):
            j = j_try
            continue
        break

    m = j - i
    p_m = pack.primes[j - 1]
    p_m1 = pack.primes[j - 2] if m >= 2 else 1

    UPm1 = UP(pack, i, j - 1)
    LOm = LO(pack, i, j)

    g_minus = L_lo_num - UPm1
    g_plus = LOm - L_hi_num

    if g_plus <= 0:
        return OutRow(y, m, p_m1, p_m, "FAIL_LO", "LO_m <= L_hi_num/DEN", UPm1, LOm, g_minus, g_plus)
    if g_minus < 0:
        return OutRow(y, m, p_m1, p_m, "FAIL_UP", "UP_{m-1} > L_lo_num/DEN", UPm1, LOm, g_minus, g_plus)

    return OutRow(y, m, p_m1, p_m, "OK", "", UPm1, LOm, g_minus, g_plus)


# =========================
# Target helpers
# =========================
def parse_ylist(s: str) -> List[int]:
    out: List[int] = []
    for tok in s.split(","):
        tok = tok.strip()
        if tok:
            out.append(int(tok))
    return out


def read_yfile(path: str) -> List[int]:
    enc = _detect_encoding(path)
    ys: List[int] = []
    with open(path, "r", encoding=enc, errors="strict") as f:
        for line in f:
            t = line.strip()
            if not t or t.startswith("#"):
                continue
            ys.append(int(t))
    return ys


# =========================
# Output
# =========================
def emit_rows(rows: List[OutRow], pack: PrefixPack, fmt: str, L_lo_num: int, L_hi_num: int) -> None:
    if fmt == "tsv":
        print("y\tm\tp_m1\tp_m\tSTATUS\tNOTE\tUPm1_num\tLOm_num\tDEN\tL_lo_num\tL_hi_num\tg_minus\tg_plus")
        for r in rows:
            note = (r.note or "").replace("\t", " ")
            print(
                f"{r.y}\t{r.m}\t{r.p_m1}\t{r.p_m}\t{r.status}\t{note}\t"
                f"{r.UPm1}\t{r.LOm}\t{pack.DEN}\t{L_lo_num}\t{L_hi_num}\t{r.g_minus}\t{r.g_plus}"
            )
        return

    if fmt == "tex":
        # Compact referee-friendly table for \input
        # 6 columns only: y, m, p_m1, p_m, g_-, g_+
        for r in rows:
            if r.status == "OK":
                print(rf"{r.y} & {r.m} & {r.p_m1} & {r.p_m} & {r.g_minus} & {r.g_plus}\\")
            else:
                # keep failure visible if ever used accidentally
                print(rf"{r.y} & \multicolumn{{5}}{{l}}{{\texttt{{{r.status}: {(r.note or '')}}}}}\\")
        return

    raise ValueError(f"Unknown format: {fmt}")


# =========================
# Main
# =========================
def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--in_tsv", required=True)
    ap.add_argument("--Y1", type=int, default=None)
    ap.add_argument("--ylist", type=str, default=None)
    ap.add_argument("--yfile", type=str, default=None)

    ap.add_argument("--prime_cap", type=int, required=True)
    ap.add_argument("--D", type=int, default=40)

    ap.add_argument("--L_lo", type=str, required=True)
    ap.add_argument("--L_hi", type=str, required=True)

    ap.add_argument("--format", choices=["tsv", "tex"], default="tsv")
    ap.add_argument("--verbose_every", type=int, default=0)
    ap.add_argument("--max_adjust", type=int, default=10000)

    args = ap.parse_args()

    cheap = read_cheap_tsv(args.in_tsv)

    if args.Y1 is not None:
        targets = sorted([y for y in cheap.keys() if 3 <= y < args.Y1])
    elif args.ylist is not None:
        targets = sorted(parse_ylist(args.ylist))
    elif args.yfile is not None:
        targets = sorted(read_yfile(args.yfile))
    else:
        targets = sorted(cheap.keys())

    if not targets:
        print("ERROR: empty target set", file=sys.stderr)
        raise SystemExit(2)

    missing = [y for y in targets if y not in cheap or cheap[y].p_m_in is None]
    if missing:
        print(f"ERROR: missing p_m for {len(missing)} y values. Example: {missing[:10]}", file=sys.stderr)
        raise SystemExit(2)

    Llo = Frac.parse(args.L_lo)
    Lhi = Frac.parse(args.L_hi)

    print(f"[sieve] sieving primes up to {args.prime_cap} ...", file=sys.stderr)
    primes = sieve_primes_upto(args.prime_cap)
    if not primes or primes[-1] < 3:
        print("ERROR: sieve produced too few primes", file=sys.stderr)
        raise SystemExit(2)

    max_pm = max(cheap[y].p_m_in for y in targets if cheap[y].p_m_in is not None)
    if primes[-1] < max_pm:
        print(f"ERROR: prime_cap too small: max prime {primes[-1]} < max(p_m) {max_pm}", file=sys.stderr)
        raise SystemExit(2)

    print(f"[prep] building prefix sums D={args.D} ...", file=sys.stderr)
    pack = build_prefixes(primes, D=args.D)

    L_lo_num = frac_floor_to_DEN(Llo, pack.DEN)
    L_hi_num = frac_ceil_to_DEN(Lhi, pack.DEN)

    out_rows: List[OutRow] = []
    total = len(targets)

    for k, y in enumerate(targets, start=1):
        p_m = cheap[y].p_m_in
        assert p_m is not None

        r = certify_one(
            pack=pack,
            y=y,
            p_m_cand=p_m,
            L_lo=Llo,
            L_hi=Lhi,
            L_lo_num=L_lo_num,
            L_hi_num=L_hi_num,
            max_adjust=args.max_adjust
        )
        out_rows.append(r)

        if args.verbose_every and (k == 1 or k % args.verbose_every == 0 or k == total):
            print(f"[{k}/{total}] y={y} p_m={p_m} status={r.status}", file=sys.stderr)

    emit_rows(out_rows, pack=pack, fmt=args.format, L_lo_num=L_lo_num, L_hi_num=L_hi_num)


if __name__ == "__main__":
    main()