# lehmer_bnb.py
# Two modes:
#   (1) --mode sieve : fast linear-window verifier (phi(n) | n-1) for odd squarefree composites
#   (2) --mode lock  : vector-pivot lock-engine on supports with inheritance L(S)=lcm(p-1)
#
# Added (lock mode):
#   --dump_frontier : grid-compressed Pareto frontier for (logI, log nS, log L)
#   --dump_inheritance : stats on marginal inheritance ratio R = lcm(L,p-1)/L
#   --dump_kstats : per-k summaries (k = |S|)

from __future__ import annotations

import argparse
import math
import time
from array import array
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple


# ---------------------------
# Prime sieve
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
            bs[start:n+1:step] = b"\x00" * (((n - start) // step) + 1)
    return [i for i in range(2, n + 1) if bs[i]]


# ---------------------------
# Basic NT helpers
# ---------------------------

def gcd(a: int, b: int) -> int:
    return math.gcd(a, b)

def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b

def is_squarefree_by_trial(n: int) -> bool:
    if n % 4 == 0:
        return False
    p = 3
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return False
        p += 2
    return True

def factor_squarefree(n: int) -> List[int]:
    fac = []
    if n % 2 == 0:
        fac.append(2)
        n //= 2
    p = 3
    while p * p <= n:
        if n % p == 0:
            fac.append(p)
            n //= p
        else:
            p += 2
    if n > 1:
        fac.append(n)
    return fac

def phi_squarefree(fac: List[int]) -> int:
    out = 1
    for p in fac:
        out *= (p - 1)
    return out

def is_lehmer_candidate_squarefree(n: int) -> bool:
    if n < 9:
        return False
    if n % 2 == 0:
        return False
    if not is_squarefree_by_trial(n):
        return False
    fac = factor_squarefree(n)
    if len(fac) <= 1:
        return False
    phi = phi_squarefree(fac)
    return ((n - 1) % phi) == 0


# ---------------------------
# Pretty table printer
# ---------------------------

def print_table(rows: List[Dict[str, str]]) -> None:
    if not rows:
        print("(no rows)")
        return
    cols = list(rows[0].keys())
    widths = {c: max(len(c), max(len(r.get(c, "")) for r in rows)) for c in cols}
    sep = "+" + "+".join("-" * (widths[c] + 2) for c in cols) + "+"
    hdr = "| " + " | ".join(c.ljust(widths[c]) for c in cols) + " |"
    print(sep)
    print(hdr)
    print(sep)
    for r in rows:
        line = "| " + " | ".join(r.get(c, "").ljust(widths[c]) for c in cols) + " |"
        print(line)
    print(sep)


# ============================================================
# MODE 1: linear sieve window verifier (fast, exhaustive window)
# ============================================================

def sieve_phi_spf_squarefree(N: int) -> Tuple[array, array, bytearray, List[int]]:
    spf = array("I", [0]) * (N + 1)
    phi = array("I", [0]) * (N + 1)
    sqf = bytearray(b"\x00") * (N + 1)

    primes: List[int] = []
    spf[1] = 1
    phi[1] = 1
    sqf[1] = 1

    for i in range(2, N + 1):
        if spf[i] == 0:
            spf[i] = i
            primes.append(i)
            phi[i] = i - 1
            sqf[i] = 1

        for p in primes:
            ip = i * p
            if ip > N:
                break
            spf[ip] = p
            if i % p == 0:
                phi[ip] = phi[i] * p
                sqf[ip] = 0
                break
            else:
                phi[ip] = phi[i] * (p - 1)
                sqf[ip] = sqf[i]

    return spf, phi, sqf, primes


def mreq_for_y_log(y: int, primes: List[int]) -> int:
    log2 = math.log(2.0)
    s = 0.0
    m = 0
    for p in primes:
        if p < y:
            continue
        s += math.log(p) - math.log(p - 1)
        m += 1
        if s > log2:
            return m
    raise ValueError("prime list too short for mreq(y)")


def run_mode_sieve(Ny: int, y_min: int, y_max: int, show_hits: bool) -> None:
    t0 = time.time()
    spf, phi, sqf, primes = sieve_phi_spf_squarefree(Ny)
    t1 = time.time()

    y_list = [p for p in primes if p >= 3 and y_min <= p <= y_max]
    tested = {y: 0 for y in y_list}
    hits = {y: 0 for y in y_list}
    first_hit = {y: 0 for y in y_list}
    all_hits: List[int] = []

    for n in range(3, Ny + 1, 2):
        y = spf[n]
        if y < y_min or y > y_max:
            continue
        if y == n:
            continue
        if sqf[n] == 0:
            continue
        tested[y] += 1
        if (n - 1) % phi[n] == 0:
            hits[y] += 1
            if first_hit[y] == 0:
                first_hit[y] = n
            all_hits.append(n)

    rows = []
    for y in y_list:
        mreq = mreq_for_y_log(y, primes)
        Wy = int(math.log(Ny) / math.log(y))
        rows.append({
            "y": str(y),
            "mreq(y)": str(mreq),
            "Wy": str(Wy),
            "tested": str(tested[y]),
            "hits": str(hits[y]),
            "first_hit": str(first_hit[y]) if first_hit[y] else "-",
        })

    print(f"Sieve up to Ny={Ny}: {len(primes)} primes in {t1 - t0:.3f}s")
    print_table(rows)

    if show_hits and all_hits:
        print("Hits:")
        for n in all_hits:
            print(n)

    print(f"Total elapsed: {time.time() - t0:.3f}s")


# ============================================================
# MODE 2: lock engine with vector pivot + inheritance
# ============================================================

@dataclass
class LockStats:
    states: int = 0
    pr_cap: int = 0
    pr_ub: int = 0
    pr_size: int = 0
    pr_gcd: int = 0
    pr_sat: int = 0
    exact_checked: int = 0
    found: int = 0

@dataclass
class KStats:
    seen: int = 0
    max_logI: float = -1e99
    min_nS: int = 0
    max_P: float = -1e99
    min_P: float = 1e99
    min_logL: float = 1e99
    max_logL: float = -1e99

def small_factor_counts(x: int, small_primes: List[int]) -> Dict[int, int]:
    out: Dict[int, int] = {}
    for p in small_primes:
        if p * p > x:
            break
        while x % p == 0:
            out[p] = out.get(p, 0) + 1
            x //= p
    if x > 1 and x in small_primes:
        out[x] = out.get(x, 0) + 1
    return out

def run_lock_for_y(
    Ny: int,
    y: int,
    primes: List[int],
    eps: float,
    max_enum_t: int,
    max_states: int,
    dump_frontier: bool,
    frontier_bins_n: int,
    frontier_bins_L: int,
    frontier_kmax: int,
    frontier_top: int,
    dump_inheritance: bool,
    inh_small_primes_max: int,
    inh_top: int,
    dump_kstats: bool,
) -> Tuple[LockStats, Optional[int], int, int, Dict[int, KStats]]:
    st = LockStats()
    log2 = math.log(2.0)

    mreq = mreq_for_y_log(y, primes)
    Wy = int(math.log(Ny) / math.log(y))

    kstats: Dict[int, KStats] = {k: KStats() for k in range(1, frontier_kmax + 1)}

    if mreq > Wy:
        return st, None, mreq, Wy, kstats

    P = [p for p in primes if p >= y and p <= Ny]
    if not P or P[0] != y:
        return st, None, mreq, Wy, kstats

    gain = [math.log(p) - math.log(p - 1) for p in P]
    pref = [0.0]
    for g in gain:
        pref.append(pref[-1] + g)

    def ub_best_from(i: int, slots: int) -> float:
        j = min(len(P), i + max(0, slots))
        return pref[j] - pref[i]

    def min_completion_product(i: int, need: int) -> int:
        prod = 1
        j = i
        for _ in range(need):
            if j >= len(P):
                return Ny + 1
            prod *= P[j]
            if prod > Ny:
                return Ny + 1
            j += 1
        return prod

    # Frontier grid: key=(k, bn, bL) -> best logI with representative nS,L
    frontier: Dict[Tuple[int, int, int], Tuple[float, int, int]] = {}

    # Inheritance stats
    R_hist: Dict[int, int] = {}
    prime_add_hist: Dict[int, int] = {}
    small_primes = [p for p in primes if p <= inh_small_primes_max]

    def update_frontier(k: int, nS: int, L: int, logI: float) -> None:
        if not dump_frontier:
            return
        if k > frontier_kmax:
            return
        ln = math.log(nS)
        lL = math.log(L) if L > 0 else 0.0
        # bins in [0, log Ny] and [0, log Ny] conservatively
        bn = min(frontier_bins_n - 1, int((ln / math.log(Ny)) * frontier_bins_n))
        bL = min(frontier_bins_L - 1, int((lL / math.log(Ny)) * frontier_bins_L))
        key = (k, bn, bL)
        cur = frontier.get(key)
        if cur is None or logI > cur[0] + 1e-15 or (abs(logI - cur[0]) <= 1e-15 and nS < cur[1]):
            frontier[key] = (logI, nS, L)

    def update_kstats(k: int, nS: int, L: int, logI: float) -> None:
        if not dump_kstats:
            return
        if k > frontier_kmax:
            return
        ks = kstats[k]
        ks.seen += 1
        if logI > ks.max_logI:
            ks.max_logI = logI
        if ks.min_nS == 0 or nS < ks.min_nS:
            ks.min_nS = nS
        if nS > 1 and L > 1:
            Ppot = math.log(L) / math.log(nS)
            ks.max_P = max(ks.max_P, Ppot)
            ks.min_P = min(ks.min_P, Ppot)
            lL = math.log(L)
            ks.min_logL = min(ks.min_logL, lL)
            ks.max_logL = max(ks.max_logL, lL)

    def record_inheritance(L_old: int, p: int, L_new: int) -> None:
        if not dump_inheritance:
            return
        if L_old == 0:
            return
        R = L_new // L_old
        if R > 1:
            R_hist[R] = R_hist.get(R, 0) + 1
            # count small primes contributed by R (rough view of new prime-power coverage)
            counts = small_factor_counts(R, small_primes)
            for q, e in counts.items():
                prime_add_hist[q] = prime_add_hist.get(q, 0) + e

    # State: (next_index, k, nS, L, logI)
    n0 = y
    L0 = y - 1
    logI0 = gain[0]
    stack: List[Tuple[int, int, int, int, float]] = [(1, 1, n0, L0, logI0)]

    found: Optional[int] = None

    while stack:
        i, k, nS, L, logI = stack.pop()
        st.states += 1
        if st.states > max_states:
            break

        # track pivot vector samples
        update_frontier(k, nS, L, logI)
        update_kstats(k, nS, L, logI)

        if nS > Ny or k > Wy:
            st.pr_cap += 1
            continue

        if k < mreq:
            need = mreq - k
            lb = nS * min_completion_product(i, need)
            if lb > Ny:
                st.pr_size += 1
                continue

        slots = Wy - k
        ub = logI + ub_best_from(i, slots)
        if ub <= log2 + 1e-15:
            st.pr_ub += 1
            continue

        if gcd(nS, L) != 1:
            st.pr_gcd += 1
            continue

        # saturation closure
        if k >= 2 and L > 1 and nS > 1:
            Ppot = math.log(L) / math.log(nS)
            if Ppot > 1.0 - eps:
                tmax = (Ny - 1) // L
                if tmax <= max_enum_t:
                    for t in range(1, tmax + 1):
                        n = 1 + t * L
                        if n % nS != 0:
                            continue
                        if n % y != 0:
                            continue
                        if is_lehmer_candidate_squarefree(n):
                            found = n
                            st.found += 1
                            break
                    if found is not None:
                        break
                    st.pr_sat += 1
                    continue

        # exact check on nS itself (support-complete candidate)
        if k >= 2 and logI > log2 + 1e-15:
            st.exact_checked += 1
            if is_lehmer_candidate_squarefree(nS):
                found = nS
                st.found += 1
                break

        # expand inclusions (combinations)
        for j in range(i, len(P)):
            p = P[j]
            n2 = nS * p
            if n2 > Ny:
                break
            L_old = L
            L2 = lcm(L, p - 1)
            record_inheritance(L_old, p, L2)
            logI2 = logI + gain[j]
            stack.append((j + 1, k + 1, n2, L2, logI2))

    # Print dumps for this y (only when y-range is tight or user wants it)
    if dump_frontier:
        rows = []
        # collect best representatives sorted by logI desc
        items = sorted(frontier.items(), key=lambda kv: kv[1][0], reverse=True)
        for (k0, bn, bL), (logI_v, n_v, L_v) in items[:frontier_top]:
            rows.append({
                "k": str(k0),
                "bin_n": str(bn),
                "bin_L": str(bL),
                "logI": f"{logI_v:.6f}",
                "nS": str(n_v),
                "L": str(L_v),
                "P": f"{(math.log(L_v)/math.log(n_v) if n_v>1 and L_v>1 else 0.0):.4f}",
            })
        print(f"\n[frontier] y={y}  (grid {frontier_bins_n}x{frontier_bins_L}, k<= {frontier_kmax}), top {frontier_top}")
        print_table(rows)

    if dump_kstats:
        rows = []
        for k0 in range(1, frontier_kmax + 1):
            ks = kstats[k0]
            if ks.seen == 0:
                continue
            rows.append({
                "k": str(k0),
                "seen": str(ks.seen),
                "max_logI": f"{ks.max_logI:.6f}" if ks.max_logI > -1e50 else "-",
                "min_nS": str(ks.min_nS) if ks.min_nS else "-",
                "minP": f"{ks.min_P:.4f}" if ks.min_P < 1e50 else "-",
                "maxP": f"{ks.max_P:.4f}" if ks.max_P > -1e50 else "-",
                "min_logL": f"{ks.min_logL:.4f}" if ks.min_logL < 1e50 else "-",
                "max_logL": f"{ks.max_logL:.4f}" if ks.max_logL > -1e50 else "-",
            })
        print(f"\n[kstats] y={y} (k<= {frontier_kmax})")
        print_table(rows)

    if dump_inheritance:
        # Top R ratios
        rowsR = []
        for R, c in sorted(R_hist.items(), key=lambda x: x[1], reverse=True)[:inh_top]:
            rowsR.append({"R": str(R), "count": str(c)})
        print(f"\n[inheritance] y={y}  Top R = lcm(L,p-1)/L (top {inh_top})")
        print_table(rowsR)

        # Top small primes added (rough)
        rowsQ = []
        for q, c in sorted(prime_add_hist.items(), key=lambda x: x[1], reverse=True)[:inh_top]:
            rowsQ.append({"q": str(q), "added_exp_total": str(c)})
        print(f"\n[inheritance] y={y}  Small prime-power mass added to L via R (q<= {inh_small_primes_max}, top {inh_top})")
        print_table(rowsQ)

    return st, found, mreq, Wy, kstats


def run_mode_lock(
    Ny: int,
    y_min: int,
    y_max: int,
    eps: float,
    prime_limit: int,
    max_enum_t: int,
    max_states: int,
    dump_frontier: bool,
    frontier_bins_n: int,
    frontier_bins_L: int,
    frontier_kmax: int,
    frontier_top: int,
    dump_inheritance: bool,
    inh_small_primes: int,
    inh_top: int,
    dump_kstats: bool,
) -> None:
    t0 = time.time()
    primes = sieve_primes_upto(min(prime_limit, Ny))
    t1 = time.time()

    y_list = [p for p in primes if p >= 3 and y_min <= p <= y_max]

    rows = []
    for y in y_list:
        st, found, mreq, Wy, _ = run_lock_for_y(
            Ny=Ny,
            y=y,
            primes=primes,
            eps=eps,
            max_enum_t=max_enum_t,
            max_states=max_states,
            dump_frontier=dump_frontier,
            frontier_bins_n=frontier_bins_n,
            frontier_bins_L=frontier_bins_L,
            frontier_kmax=frontier_kmax,
            frontier_top=frontier_top,
            dump_inheritance=dump_inheritance,
            inh_small_primes_max=inh_small_primes,
            inh_top=inh_top,
            dump_kstats=dump_kstats,
        )

        rows.append({
            "y": str(y),
            "mreq(y)": str(mreq),
            "Wy": str(Wy),
            "states": str(st.states),
            "prCap": str(st.pr_cap),
            "prUB": str(st.pr_ub),
            "prSize": str(st.pr_size),
            "prGCD": str(st.pr_gcd),
            "prSat": str(st.pr_sat),
            "exact": str(st.exact_checked),
            "found": str(found) if found else "-",
        })
        if found:
            break

    print(f"Prime sieve up to {min(prime_limit, Ny)}: {len(primes)} primes in {t1 - t0:.3f}s")
    print(f"LOCK mode: Ny={Ny}, y in [{y_min},{y_max}], eps={eps}, max_enum_t={max_enum_t}, max_states={max_states}")
    print_table(rows)
    print(f"Total elapsed: {time.time() - t0:.3f}s")


# ---------------------------
# CLI
# ---------------------------

def main() -> None:
    ap = argparse.ArgumentParser(description="Lehmer finite-window verifier + vector-pivot lock-engine.")
    ap.add_argument("--mode", choices=["sieve", "lock"], default="sieve")
    ap.add_argument("--Ny", type=int, default=10_000_000)
    ap.add_argument("--y_min", type=int, default=3)
    ap.add_argument("--y_max", type=int, default=97)

    # sieve mode
    ap.add_argument("--show_hits", action="store_true")

    # lock mode core
    ap.add_argument("--eps", type=float, default=0.08)
    ap.add_argument("--prime_limit", type=int, default=10_000_000)
    ap.add_argument("--max_enum_t", type=int, default=250000)
    ap.add_argument("--max_states", type=int, default=2_000_000)

    # lock dumps
    ap.add_argument("--dump_frontier", action="store_true")
    ap.add_argument("--frontier_bins_n", type=int, default=60)
    ap.add_argument("--frontier_bins_L", type=int, default=60)
    ap.add_argument("--frontier_kmax", type=int, default=14)
    ap.add_argument("--frontier_top", type=int, default=80)

    ap.add_argument("--dump_inheritance", action="store_true")
    ap.add_argument("--inh_small_primes", type=int, default=97)
    ap.add_argument("--inh_top", type=int, default=30)

    ap.add_argument("--dump_kstats", action="store_true")

    args = ap.parse_args()

    if args.mode == "sieve":
        run_mode_sieve(args.Ny, args.y_min, args.y_max, args.show_hits)
    else:
        run_mode_lock(
            Ny=args.Ny,
            y_min=args.y_min,
            y_max=args.y_max,
            eps=args.eps,
            prime_limit=args.prime_limit,
            max_enum_t=args.max_enum_t,
            max_states=args.max_states,
            dump_frontier=args.dump_frontier,
            frontier_bins_n=args.frontier_bins_n,
            frontier_bins_L=args.frontier_bins_L,
            frontier_kmax=args.frontier_kmax,
            frontier_top=args.frontier_top,
            dump_inheritance=args.dump_inheritance,
            inh_small_primes=args.inh_small_primes,
            inh_top=args.inh_top,
            dump_kstats=args.dump_kstats,
        )


if __name__ == "__main__":
    main()
