#!/usr/bin/env python3
# appendixB_table_generator.py

import argparse
import bisect
import csv
import math
import re
import sys
import time
from fractions import Fraction
from pathlib import Path
from math import gcd

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

YC = 2000
YSTAR = 30000
LN2_TERMS = 80
LOG_INTERVAL_TERMS = 80


def progress(i, n, label="", width=32):
    if n <= 0:
        return
    frac = i / n
    filled = int(width * frac)
    bar = "#" * filled + "-" * (width - filled)
    pct = 100 * frac
    sys.stderr.write(f"\r{label} [{bar}] {i}/{n} ({pct:5.1f}%)")
    sys.stderr.flush()
    if i == n:
        sys.stderr.write("\n")


def read_text_any_encoding(path: str) -> str:
    raw = Path(path).read_bytes()
    for enc in ("utf-8-sig", "utf-16", "utf-16-le", "utf-16-be", "cp1252"):
        try:
            text = raw.decode(enc)
            if "Case C pivot rows" in text or "y,mreq_y" in text:
                return text
        except UnicodeDecodeError:
            pass
    return raw.decode("utf-8", errors="replace")


def ceil_fraction(fr: Fraction) -> int:
    return (fr.numerator + fr.denominator - 1) // fr.denominator


def primes_upto(n: int):
    if n < 2:
        return []
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"
    p = 2
    while p * p <= n:
        if sieve[p]:
            start = p * p
            step = p
            sieve[start:n + 1:step] = b"\x00" * (((n - start) // step) + 1)
        p += 1
    return [i for i in range(n + 1) if sieve[i]]


def is_prime_trial(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def ln2_interval(terms: int):
    s = Fraction(0, 1)
    for k in range(terms):
        s += Fraction(2, (2 * k + 1) * 3 ** (2 * k + 1))

    tail = (
        Fraction(2, (2 * terms + 1) * 3 ** (2 * terms + 1))
        * Fraction(1, 1 - Fraction(1, 9))
    )
    return s, s + tail


def log_r_interval_atanh(r: Fraction, terms: int):
    if not (Fraction(1, 1) <= r < Fraction(2, 1)):
        raise ValueError("requires 1 <= r < 2")

    z = (r - 1) / (r + 1)
    if z == 0:
        return Fraction(0, 1), Fraction(0, 1)

    s = Fraction(0, 1)
    zpow = z

    for j in range(terms):
        s += Fraction(2, 1) * zpow / (2 * j + 1)
        zpow *= z * z

    tail = Fraction(2, 1) * zpow / (2 * terms + 1) * Fraction(1, 1) / (1 - z * z)
    return s, s + tail


def log_int_interval(n: int):
    if n <= 0:
        raise ValueError("log_int_interval requires n > 0")

    k = n.bit_length() - 1
    two_k = 1 << k
    r = Fraction(n, two_k)

    ln2_lb, ln2_ub = ln2_interval(LN2_TERMS)
    lr_lb, lr_ub = log_r_interval_atanh(r, LOG_INTERVAL_TERMS)

    return k * ln2_lb + lr_lb, k * ln2_ub + lr_ub


def certified_M_upper_from_manuscript(y: int):
    """
    M(y) = ceil((3/20) * y/log(y)) + ceil(3*(log y)^4).

    Certified upper integer:
      log_lower <= log(y) <= log_upper.
    """
    log_lb, log_ub = log_int_interval(y)

    W_upper = ceil_fraction(Fraction(3 * y, 20) / log_lb)
    K_upper = ceil_fraction(3 * (log_ub ** 4))

    return W_upper + K_upper


def build_log_prefix(primes):
    prefix = [0.0]
    acc = 0.0
    for p in primes:
        acc += -math.log1p(-1.0 / p)
        prefix.append(acc)
    return prefix


def mreq_log(y: int, primes, prefix):
    idx = bisect.bisect_left(primes, y)
    if idx >= len(primes):
        raise RuntimeError(f"Prime pool starts too low for y={y}")

    target = prefix[idx] + math.log(2.0)
    k = bisect.bisect_right(prefix, target)
    if k >= len(prefix):
        raise RuntimeError(f"Prime pool too small for y={y}")

    m = k - idx
    prev_sum = prefix[idx + m - 1] - prefix[idx]
    cur_sum = prefix[idx + m] - prefix[idx]

    prev_margin = math.log(2.0) - prev_sum
    margin = cur_sum - math.log(2.0)

    return m, primes[idx], primes[idx + m - 1], prev_margin, margin


def ensure_prime_pool_for_caseC(caseC_primes):
    max_y = max(caseC_primes)
    limit = max(200000, 4 * max_y * max_y)

    while True:
        t0 = time.time()
        print(f"[pool] sieving primes up to {limit} ...", file=sys.stderr)

        primes = primes_upto(limit)
        prefix = build_log_prefix(primes)

        ok = True
        for y in caseC_primes:
            try:
                mreq_log(y, primes, prefix)
            except RuntimeError:
                ok = False
                break

        if ok:
            print(
                f"[pool] ready: {len(primes)} primes, limit={limit}, time={time.time()-t0:.2f}s",
                file=sys.stderr,
            )
            return primes, prefix

        limit *= 2


def multiply_reduced(num: int, den: int, a: int, b: int):
    g = gcd(a, den)
    a //= g
    den //= g

    g = gcd(b, num)
    b //= g
    num //= g

    return num * a, den * b


def verify_casec_rows_exact_sliding(rows, primes):
    rows = sorted(rows, key=lambda r: r[0])
    num = 1
    den = 1
    cur_start = None
    cur_end = None

    print("\n[B.2 exact certificate from Case C table]")
    print("y,mreq_y,first_prime,last_prime,num_bits,den_bits,status")

    for i, (y, m, first_p, last_p) in enumerate(rows, 1):
        progress(i, len(rows), "Exact Case C")

        if not is_prime_trial(y):
            raise AssertionError(f"Non-prime y in Case C table: {y}")
        if not (3 <= y < YC):
            raise AssertionError(f"y outside Case C range: {y}")
        if m <= 0:
            raise AssertionError(f"Invalid mreq_y at y={y}: {m}")

        target_start = bisect.bisect_left(primes, y)
        target_end = target_start + m - 1

        if target_end >= len(primes):
            raise RuntimeError(f"Prime pool too small at y={y}")

        if primes[target_start] != first_p:
            raise AssertionError(
                f"first_prime mismatch at y={y}: table={first_p}, exact={primes[target_start]}"
            )

        if primes[target_end] != last_p:
            raise AssertionError(
                f"last_prime mismatch at y={y}: table={last_p}, exact={primes[target_end]}"
            )

        if cur_start is None:
            cur_start = target_start
            cur_end = target_start - 1
            num = 1
            den = 1

        while cur_start < target_start:
            p = primes[cur_start]
            num, den = multiply_reduced(num, den, p - 1, p)
            cur_start += 1

        while cur_start > target_start:
            cur_start -= 1
            p = primes[cur_start]
            num, den = multiply_reduced(num, den, p, p - 1)

        while cur_end < target_end:
            cur_end += 1
            p = primes[cur_end]
            num, den = multiply_reduced(num, den, p, p - 1)

        while cur_end > target_end:
            p = primes[cur_end]
            num, den = multiply_reduced(num, den, p - 1, p)
            cur_end -= 1

        last = primes[target_end]
        right_ok = num > 2 * den
        left_ok = num * (last - 1) <= 2 * den * last

        if not (left_ok and right_ok):
            raise AssertionError(f"Exact pivot certificate failed at y={y}")

        print(f"{y},{m},{first_p},{last_p},{num.bit_length()},{den.bit_length()},PASS")

    print(f"\nchecked {len(rows)} Case C rows: PASS exact sliding certificate")


def load_casec_table(path: str):
    p = Path(path)
    if not p.exists():
        raise FileNotFoundError(path)

    text = read_text_any_encoding(path)
    row_re = re.compile(
        r"^\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)(?:\s*,.*)?\s*$",
        re.MULTILINE,
    )

    rows = []
    for mobj in row_re.finditer(text):
        y = int(mobj.group(1))
        m = int(mobj.group(2))
        first_p = int(mobj.group(3))
        last_p = int(mobj.group(4))
        if 3 <= y < YC:
            rows.append((y, m, first_p, last_p))

    if not rows:
        preview = "\n".join(text.splitlines()[:40])
        raise ValueError("No Case C rows found. First 40 lines were:\n" + preview)

    return rows


def verify_casec_table_exact(path: str):
    rows = load_casec_table(path)
    y_values = [r[0] for r in rows]
    y_set = set(y_values)

    expected_primes = [p for p in primes_upto(YC - 1) if p >= 3]
    expected_set = set(expected_primes)

    if len(rows) != len(y_set):
        raise AssertionError("Duplicate y values found in Case C table")

    missing = sorted(expected_set - y_set)
    extra = sorted(y_set - expected_set)

    if missing:
        raise AssertionError(f"Missing Case C primes: {missing[:20]}")
    if extra:
        raise AssertionError(f"Extra y values outside Case C prime range: {extra[:20]}")

    max_last = max(r[3] for r in rows)
    limit = max(200000, max_last + 1000)

    print(f"[exact] sieving primes up to {limit} ...", file=sys.stderr)
    primes = primes_upto(limit)

    if primes[-1] < max_last:
        raise RuntimeError("Prime sieve failed to cover last_prime range")

    verify_casec_rows_exact_sliding(rows, primes)
    print("FINAL STATUS: PASS")


def write_casec_csv(path: str, rows):
    with open(path, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["y", "mreq_y", "first_prime", "last_prime", "prev_margin", "margin"])
        for y, m, first_p, last_p, prev_margin, margin in rows:
            writer.writerow([y, m, first_p, last_p, f"{prev_margin:.18e}", f"{margin:.18e}"])


def verify_ub_m_le_2(y: int, M: int, primes):
    """
    Certifies exactly:
      UB_M(y) <= 2.

    This proves:
      M < m_req(y).
    """
    start = bisect.bisect_left(primes, y)
    end = start + M

    if end > len(primes):
        raise RuntimeError(f"Prime pool too small for y={y}, M={M}")

    num = 1
    den = 1

    for p in primes[start:end]:
        num, den = multiply_reduced(num, den, p, p - 1)

    ok = num <= 2 * den

    return {
        "ok": ok,
        "first_prime": primes[start],
        "last_prime": primes[end - 1],
        "num_bits": num.bit_length(),
        "den_bits": den.bit_length(),
    }


def verify_transition_direct_chunk(transition_primes, chunk_id, chunk_count, out_path):
    if out_path is None:
        raise ValueError("--out is required with --transition-direct-chunk")

    if not (0 <= chunk_id < chunk_count):
        raise ValueError("chunk_id must satisfy 0 <= chunk_id < chunk_count")

    rows = []
    for i, y in enumerate(transition_primes):
        if i % chunk_count == chunk_id:
            rows.append(y)

    if not rows:
        raise ValueError("empty transition chunk")

    max_y = max(rows)
    max_M = max(certified_M_upper_from_manuscript(y) for y in rows)
    limit = max(200000, max_y + 20 * max_M)

    while True:
        print(f"[direct] sieving primes up to {limit} ...", file=sys.stderr)
        primes = primes_upto(limit)

        try:
            with open(out_path, "w", newline="") as f:
                writer = csv.writer(f)
                writer.writerow([
                    "y",
                    "M_cert",
                    "first_prime",
                    "last_prime",
                    "num_bits",
                    "den_bits",
                    "status",
                ])

                for j, y in enumerate(rows, 1):
                    progress(j, len(rows), f"Transition direct chunk {chunk_id}/{chunk_count}")

                    M = certified_M_upper_from_manuscript(y)
                    cert = verify_ub_m_le_2(y, M, primes)

                    if not cert["ok"]:
                        raise AssertionError(f"UB_M(y) <= 2 failed at y={y}, M={M}")

                    writer.writerow([
                        y,
                        M,
                        cert["first_prime"],
                        cert["last_prime"],
                        cert["num_bits"],
                        cert["den_bits"],
                        "PASS",
                    ])

            print(f"\nwrote {out_path}")
            print(f"checked {len(rows)} transition rows: PASS")
            print("FINAL STATUS: PASS")
            return

        except RuntimeError:
            limit *= 2


def merge_transition_direct(paths, transition_primes):
    table = {}

    for path in paths:
        with open(path, newline="") as f:
            reader = csv.DictReader(f)
            required = {"y", "M_cert", "status"}

            if reader.fieldnames is None or not required.issubset(set(reader.fieldnames)):
                raise ValueError(f"{path} must contain columns y,M_cert,status")

            for row in reader:
                y = int(row["y"])

                if y in table:
                    raise AssertionError(f"Duplicate transition y={y}")

                if row["status"] != "PASS":
                    raise AssertionError(f"Non-PASS row at y={y} in {path}")

                table[y] = row

    expected = set(transition_primes)
    actual = set(table)

    missing = sorted(expected - actual)
    extra = sorted(actual - expected)

    if missing:
        raise AssertionError(f"Missing transition primes: {missing[:20]}")
    if extra:
        raise AssertionError(f"Extra transition rows: {extra[:20]}")

    for y in actual:
        if not is_prime_trial(y):
            raise AssertionError(f"Non-prime transition row: {y}")
        if not (YC <= y < YSTAR):
            raise AssertionError(f"Out-of-range transition row: {y}")

    print("Transition direct merge")
    print(f"rows: {len(table)}")
    print("coverage: PASS")
    print("duplicates: PASS")
    print("range: PASS")
    print("primality: PASS")
    print("comparison: PASS")
    print("FINAL STATUS: PASS")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--exact-casec", action="store_true")
    parser.add_argument("--verify-casec-table", type=str, default=None)
    parser.add_argument("--write-casec-csv", type=str, default=None)

    parser.add_argument("--transition-direct-chunk", nargs=2, type=int, default=None)
    parser.add_argument("--out", type=str, default=None)
    parser.add_argument("--merge", nargs="*", default=None)

    args = parser.parse_args()

    initial_primes = primes_upto(YSTAR)
    caseC_primes = [p for p in initial_primes if 3 <= p < YC]
    transition_primes = [p for p in initial_primes if YC <= p < YSTAR]

    assert len(caseC_primes) == len(set(caseC_primes))
    assert len(transition_primes) == len(set(transition_primes))
    assert all(3 <= y < YC for y in caseC_primes)
    assert all(YC <= y < YSTAR for y in transition_primes)

    for y in caseC_primes + transition_primes:
        assert is_prime_trial(y), f"Non-prime listed as pivot: {y}"

    if args.verify_casec_table is not None:
        verify_casec_table_exact(args.verify_casec_table)
        return

    if args.transition_direct_chunk is not None:
        chunk_id, chunk_count = args.transition_direct_chunk
        verify_transition_direct_chunk(
            transition_primes,
            chunk_id,
            chunk_count,
            args.out,
        )
        if args.merge:
            merge_transition_direct(args.merge, transition_primes)
        return

    if args.merge:
        merge_transition_direct(args.merge, transition_primes)
        return

    print("Appendix B table generation and verification")
    print("+--------------------------------------+----------------------+")
    print(f"| YC                                   | {YC:<20} |")
    print(f"| YSTAR                                | {YSTAR:<20} |")
    print(f"| ln2_terms                            | {LN2_TERMS:<20} |")
    print(f"| exact Case C integer check           | {str(args.exact_casec):<20} |")
    print("+--------------------------------------+----------------------+")

    print(f"Case C primes: {len(caseC_primes)}")
    print(f"Transition primes: {len(transition_primes)}")

    ln2_lb, ln2_ub = ln2_interval(LN2_TERMS)
    assert ln2_lb < ln2_ub

    print("\n[B.1] log(2) enclosure")
    print(f"lower = {ln2_lb.numerator}/{ln2_lb.denominator}")
    print(f"upper = {ln2_ub.numerator}/{ln2_ub.denominator}")
    print("check  = PASS")

    print("\n[B.2] finite pivot table checks")
    primes, prefix = ensure_prime_pool_for_caseC(caseC_primes)
    pivot_rows = []

    for i, y in enumerate(caseC_primes, 1):
        progress(i, len(caseC_primes), "Case C pivots")
        m, first_p, last_p, prev_margin, margin = mreq_log(y, primes, prefix)

        if prev_margin <= 0 or margin <= 0:
            raise AssertionError(
                f"Log pivot boundary not separated at y={y}: "
                f"prev_margin={prev_margin}, margin={margin}"
            )

        pivot_rows.append((y, m, first_p, last_p, prev_margin, margin))

    if args.exact_casec:
        exact_rows = [(y, m, first_p, last_p) for y, m, first_p, last_p, _, _ in pivot_rows]
        verify_casec_rows_exact_sliding(exact_rows, primes)

    if args.write_casec_csv is not None:
        write_casec_csv(args.write_casec_csv, pivot_rows)
        print(f"\nwrote Case C CSV: {args.write_casec_csv}")

    print("\nCase C pivot rows:")
    print("y,mreq_y,first_prime,last_prime,prev_margin,margin")
    for y, m, first_p, last_p, prev_margin, margin in pivot_rows:
        print(f"{y},{m},{first_p},{last_p},{prev_margin:.18e},{margin:.18e}")

    print(f"\nchecked {len(pivot_rows)} Case C pivot rows: PASS")
    print("\n[B.3] finite transition direct certificate")
    print("Available commands:")
    print("  python appendixB_table_generator.py --transition-direct-chunk 0 3 --out transition_direct_0.csv")
    print("  python appendixB_table_generator.py --transition-direct-chunk 1 3 --out transition_direct_1.csv")
    print("  python appendixB_table_generator.py --transition-direct-chunk 2 3 --out transition_direct_2.csv")
    print("  python appendixB_table_generator.py --merge transition_direct_0.csv transition_direct_1.csv transition_direct_2.csv")
    print("\nFINAL STATUS: PASS")


if __name__ == "__main__":
    main()