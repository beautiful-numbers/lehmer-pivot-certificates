#!/usr/bin/env python3
# make_transition_blocks_tex.py
#
# Builds the compact Appendix B transition block table using the UP_60
# certificate, not the huge rational product certificate.
#
# Input default:
#   transition_direct_0.csv
#   transition_direct_1.csv
#   transition_direct_2.csv
#
# Output:
#   appB_transition_blocks_YC_2000_YSTAR_30000.tex
#
# Each LaTeX row:
#   a & b & M_B & p_{a,M_B} & g_tr \\
#
# where:
#   M_B  = max M(y) over prime pivots y in the block [a,b],
#   p_{a,M_B} is the M_B-th prime >= a,
#   g_tr = L60_MINUS - UP60(i_a, i_a + M_B) >= 0.

import argparse
import bisect
import csv
import sys
from pathlib import Path

YC = 2000
YSTAR = 30000

D = 40
S = 10 ** D
DEN60 = 60 * S

L60_MINUS = 415888308335967185650339272874905940845300
L60_PLUS = 415888308335967185650339272874905940845301

OUT_TEX = "appB_transition_blocks_YC_2000_YSTAR_30000.tex"

DEFAULT_CHUNKS = [
    "transition_direct_0.csv",
    "transition_direct_1.csv",
    "transition_direct_2.csv",
]


def ceil_div(a: int, b: int) -> int:
    return -(-a // b)


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


def up60_contribution(p: int) -> int:
    """
    Appendix B UP_60 contribution for one prime p>=3.

    q = p-1

    uU1 = ceil(S / q)
    uL2 = floor(S / q**2)
    uU3 = ceil(S / q**3)
    uL4 = floor(S / q**4)
    uU5 = ceil(S / q**5)

    contribution:
      60*uU1 - 30*uL2 + 20*uU3 - 15*uL4 + 12*uU5
    """
    if p < 3:
        raise ValueError(f"UP60 contribution requires p>=3, got p={p}")

    q = p - 1

    uU1 = ceil_div(S, q)
    uL2 = S // (q ** 2)
    uU3 = ceil_div(S, q ** 3)
    uL4 = S // (q ** 4)
    uU5 = ceil_div(S, q ** 5)

    return 60 * uU1 - 30 * uL2 + 20 * uU3 - 15 * uL4 + 12 * uU5


def build_up60_prefix(primes):
    prefix = [0]

    for i, p in enumerate(primes, 1):
        progress(i, len(primes), "UP60 prefix")

        if p < 3:
            contrib = 0
        else:
            contrib = up60_contribution(p)

        prefix.append(prefix[-1] + contrib)

    return prefix


def up60_range(prefix, i: int, j: int) -> int:
    """
    UP60(i,j) = sum contribution(prime[t]) for t in [i,j).
    """
    if i < 0 or j < i or j > len(prefix) - 1:
        raise IndexError(f"Invalid UP60 range [{i},{j})")
    return prefix[j] - prefix[i]


def read_chunks(paths):
    """
    Reads transition direct chunk files.

    Required columns:
      y
      status

    M column accepted under:
      M_cert, M, or M_y.

    Rejected if status != PASS exactly.
    """
    table = {}

    for path in paths:
        p = Path(path)
        if not p.exists():
            raise FileNotFoundError(path)

        with p.open(newline="") as f:
            reader = csv.DictReader(f)

            if reader.fieldnames is None:
                raise ValueError(f"{path}: missing CSV header")

            fields = set(reader.fieldnames)

            if "y" not in fields:
                raise ValueError(f"{path}: missing column y")

            if "status" not in fields:
                raise ValueError(f"{path}: missing column status")

            m_col = None
            for candidate in ("M_cert", "M", "M_y"):
                if candidate in fields:
                    m_col = candidate
                    break

            if m_col is None:
                raise ValueError(f"{path}: missing M column, expected M_cert, M, or M_y")

            for row in reader:
                y_raw = row.get("y", "").strip()
                if not y_raw:
                    continue

                status = row["status"].strip()
                if status != "PASS":
                    raise AssertionError(f"{path}: non-PASS row at y={y_raw}")

                y = int(y_raw)
                M = int(row[m_col])

                if y in table:
                    raise AssertionError(f"Duplicate y={y} across chunks")

                table[y] = M

    return table


def verify_transition_rows(table, transition_primes):
    expected = set(transition_primes)
    actual = set(table)

    missing = sorted(expected - actual)
    extra = sorted(actual - expected)

    if missing:
        raise AssertionError(f"Missing transition primes: {missing[:20]}")

    if extra:
        raise AssertionError(f"Extra transition rows: {extra[:20]}")

    for y in sorted(actual):
        if not (YC <= y < YSTAR):
            raise AssertionError(f"Out-of-range y={y}")

        if not is_prime_trial(y):
            raise AssertionError(f"Non-prime y={y}")

        if table[y] <= 0:
            raise AssertionError(f"Non-positive M value at y={y}: {table[y]}")


def ensure_prime_pool(transition_primes, M_table):
    """
    Builds enough primes to evaluate UP60(i_a, i_a + M_B) for all possible blocks.

    Starts at:
      max(200000, YSTAR + 20*max_M)

    If not enough, doubles.
    """
    max_M = max(M_table.values())
    max_y = max(transition_primes)
    limit = max(200000, YSTAR + 20 * max_M)

    while True:
        print(f"[sieve] primes up to {limit} ...", file=sys.stderr)
        primes = primes_upto(limit)

        enough = True
        for y in transition_primes:
            i = bisect.bisect_left(primes, y)
            if i >= len(primes) or primes[i] != y:
                enough = False
                break
            if i + max_M > len(primes):
                enough = False
                break

        if enough:
            return primes

        limit *= 2


def build_blocks_greedy(transition_primes, M_table, primes, up_prefix):
    """
    Greedy maximal block construction.

    For candidate block [a,b]:

      M_B = max M(y) over prime y in [a,b]
      g_tr = L60_MINUS - UP60(i_a, i_a + M_B)

    The block is valid iff g_tr >= 0.
    """
    blocks = []
    n = len(transition_primes)
    i = 0

    while i < n:
        a = transition_primes[i]
        i_a = bisect.bisect_left(primes, a)

        if i_a >= len(primes) or primes[i_a] != a:
            raise AssertionError(f"Prime pool mismatch at block start a={a}")

        cur_M_B = 0
        best = None
        j = i

        while j < n:
            y = transition_primes[j]
            cur_M_B = max(cur_M_B, M_table[y])

            end = i_a + cur_M_B
            if end > len(primes):
                raise RuntimeError(f"Prime pool too small for a={a}, M_B={cur_M_B}")

            up = up60_range(up_prefix, i_a, end)
            g_tr = L60_MINUS - up

            if g_tr < 0:
                break

            best = {
                "a": a,
                "b": y,
                "M_B": cur_M_B,
                "last_prime": primes[end - 1],
                "g_tr": g_tr,
                "count": j - i + 1,
            }

            j += 1

        if best is None:
            M = M_table[a]
            end = i_a + M
            up = up60_range(up_prefix, i_a, end)
            g_tr = L60_MINUS - up
            raise AssertionError(f"Singleton transition block failed at a={a}, M={M}, g_tr={g_tr}")

        blocks.append(best)
        progress(len(blocks), n, "Blocks built")

        i += best["count"]

    sys.stderr.write("\n")
    return blocks


def verify_blocks_independent(blocks, transition_primes, M_table, primes, up_prefix):
    """
    Independent verification after greedy construction.

    Checks:
      - ordered blocks;
      - disjoint blocks;
      - exact coverage;
      - M_B = max M(y);
      - g_tr = L60_MINUS - UP60(i_a, i_a+M_B);
      - g_tr >= 0.
    """
    covered = []
    previous_b = None

    for block in blocks:
        a = block["a"]
        b = block["b"]
        M_B = block["M_B"]
        g_tr = block["g_tr"]
        last_prime = block["last_prime"]

        if previous_b is not None and a <= previous_b:
            raise AssertionError(f"Blocks are not strictly ordered at a={a}")

        if not (YC <= a <= b < YSTAR):
            raise AssertionError(f"Invalid block range [{a},{b}]")

        block_primes = [y for y in transition_primes if a <= y <= b]

        if not block_primes:
            raise AssertionError(f"Empty block [{a},{b}]")

        if block_primes[0] != a:
            raise AssertionError(f"Block start a={a} is not first prime in block")

        if block_primes[-1] != b:
            raise AssertionError(f"Block end b={b} is not last prime in block")

        expected_M_B = max(M_table[y] for y in block_primes)

        if M_B != expected_M_B:
            raise AssertionError(
                f"M_B mismatch for block [{a},{b}]: "
                f"stored={M_B}, expected={expected_M_B}"
            )

        i_a = bisect.bisect_left(primes, a)
        if i_a >= len(primes) or primes[i_a] != a:
            raise AssertionError(f"Prime pool mismatch at a={a}")

        end = i_a + M_B
        if end > len(primes):
            raise RuntimeError(f"Prime pool too small in verification for [{a},{b}]")

        expected_last_prime = primes[end - 1]
        if last_prime != expected_last_prime:
            raise AssertionError(
                f"last_prime mismatch for block [{a},{b}]: "
                f"stored={last_prime}, expected={expected_last_prime}"
            )

        expected_g_tr = L60_MINUS - up60_range(up_prefix, i_a, end)

        if g_tr != expected_g_tr:
            raise AssertionError(
                f"g_tr mismatch for block [{a},{b}]: "
                f"stored={g_tr}, expected={expected_g_tr}"
            )

        if g_tr < 0:
            raise AssertionError(f"Negative g_tr for block [{a},{b}]: {g_tr}")

        covered.extend(block_primes)
        previous_b = b

    if covered != transition_primes:
        raise AssertionError("Blocks do not cover transition primes exactly and in order")


def write_latex_blocks(path, blocks):
    """
    Writes table body only:

      a & b & M_B & p_{a,M_B} & g_tr \\
    """
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        for block in blocks:
            f.write(
                f"{block['a']} & "
                f"{block['b']} & "
                f"{block['M_B']} & "
                f"{block['last_prime']} & "
                f"{block['g_tr']} \\\\\n"
            )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("chunks", nargs="*", default=DEFAULT_CHUNKS)
    parser.add_argument("--out", type=str, default=OUT_TEX)
    args = parser.parse_args()

    transition_primes = [p for p in primes_upto(YSTAR - 1) if YC <= p < YSTAR]

    M_table = read_chunks(args.chunks)
    verify_transition_rows(M_table, transition_primes)

    primes = ensure_prime_pool(transition_primes, M_table)
    up_prefix = build_up60_prefix(primes)

    blocks = build_blocks_greedy(transition_primes, M_table, primes, up_prefix)
    verify_blocks_independent(blocks, transition_primes, M_table, primes, up_prefix)

    min_g_tr = min(block["g_tr"] for block in blocks)

    write_latex_blocks(args.out, blocks)

    print("Transition UP60 block LaTeX generation")
    print(f"transition primes: {len(transition_primes)}")
    print(f"rows read: {len(M_table)}")
    print(f"blocks produced: {len(blocks)}")
    print(f"minimum g_tr: {min_g_tr}")
    print(f"wrote: {args.out}")
    print("FINAL STATUS: PASS")


if __name__ == "__main__":
    main()