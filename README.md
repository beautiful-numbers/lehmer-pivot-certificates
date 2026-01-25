# Lehmer Totient (Pivot Method) — Companion Code & Certificates

Companion code and certificates for the paper:

**“Lehmer’s Totient Problem and a Prime Cost Pivot Method”**  
(archived on Zenodo; this GitHub repository contains *only* code + certificate artefacts, not the paper source).

This repository is designed for **referees**:
- run a few **short, deterministic commands** (no external packages),
- regenerate the **key constants / tables** used in the appendices,
- verify that the **frozen certificate files** in `certificates/` match the published hashes.

All computations use **exact rational / integer arithmetic** where needed and print **auditable** intermediate values.

---

## ✅ What’s included (curated)

### Code
- `code/compute_Y1.py`  
  Generates the Appendix **A** “pivot” artefacts and the Appendix **D** finite Case B sanity scan.  
  It can compute `mreq(y)` **exactly** on a finite range, or by an **analytic lower bound** beyond a threshold `Y0`,
  and it can output self-contained “endpoint proof-check” reports.

- `code/lehmer_bnb.py`  
  A finite-window verifier and a support-based enumeration engine (“sieve + lock”).  
  It is also the generator / checker for the Appendix C branch-and-bound transcript shipped in `certificates/appendixC/`.

### Certificates (minimal set needed by the paper text)
- **Appendix A (pivot artefacts)**  
  - `certificates/appendixA/pivot_only_y3_200.txt`  
  - `certificates/appendixA/pivotA_proof_Y0=30000.txt`

- **Appendix A.4 (small range 3 ≤ y < Y0 exact table)**
  - `certificates/mreq/mreq_exact_primes_3_to_30000.txt`
  - `certificates/mreq/mreq_exact_3_to_30000_L50000000.txt`
 
- **Appendix C (finite verification infrastructure: transcript + summary)**
  - `certificates/appendixC/summary.json`
  - `certificates/appendixC/transcript.jsonl`

- **Appendix D (Case B finite sanity scan; explicitly non-logical)**  
  - `certificates/appendixD/caseB_sanity_scan.txt`

Everything else (extra prime-limit variants, eps-variants) is **optional** and can be kept out to avoid clutter.

---

## Quickstart (referee workflow)

### Requirements
- Python 3.10+ recommended.
- No external Python packages.

### 1) Verify certificate integrity (hash check)
This checks that the artefacts in `certificates/` are exactly the ones published.

```bash
cd certificates
sha256sum -c manifest.sha256
```

Expected result: every line ends with `OK`.

This checks *only integrity* (files unchanged), not mathematical correctness.

---

### 2) Verify Appendix C (branch-and-bound transcript replay)

Run the checker/replay:

```bash
python3 code/lehmer_bnb.py --mode check_transcript \
  --summary certificates/appendixC/summary.json
```

Expected result: PASS (exit code 0).

---

## Appendix-by-appendix: what each artefact proves and how to regenerate it

This section explains **why each file exists** and **exactly which appendix claim it supports**.

---

# Appendix A — Pivot constants and endpoint check

Appendix A contains two types of finite evidence:

1) **a small pivot-only table excerpt** (to show the exact computation format and to enable quick spot checks), and  
2) **a standalone endpoint check at y = Y0** (the critical finite inequality verification that justifies the switch
   to the analytic lower bound beyond `Y0`).

Both are produced by `code/compute_Y1.py`.

---

## A1. `certificates/appendixA/pivot_only_y3_200.txt`  (pivot-only excerpt)

**What it contains.**  
A compact table for primes \(y \in [3,200]\) listing the certified status and the exact value `mreq(y)`.

**What it supports in Appendix A.**  
It demonstrates that the “pivot quantity” `mreq(y)` is computed in a **finite, independently checkable** way
(using exact arithmetic and certified inequality tests), and it provides a small-range excerpt suitable for
manual inspection.

**How to regenerate (optional).**
```bash
python3 code/compute_Y1.py \
  --mode pivot_only \
  --y_min 3 --y_max 200 \
  --mreq_mode exact \
  --prime_limit 1000000 \
  > certificates/appendixA/pivot_only_y3_200.txt
```

## A2. `certificates/appendixA/pivotA_proof_Y0=30000.txt`  (endpoint proof-check)

**What it contains.**  
A self-contained report that checks the Appendix A endpoint inequality at **\(y = Y_0 = 30000\)**.
The report prints all intermediate quantities used in the bound (e.g., the chosen Mertens-type difference bound,
nth-prime bound parameters, error terms) and ends with a single YES/NO verdict plus a SHA256 line.

**What it supports in Appendix A.**  
This file is the “referee-ready” finite verification that the bound required to certify the analytic branch is
valid at the endpoint \(y=Y_0\). In the paper’s logic, this is the place where a referee should *not* be asked to
trust “we checked it numerically”: the report shows the full inequality evaluation.

**How to regenerate (optional).**  
You must use the *same constants* as in the paper (the reference strings are printed for audit clarity).
```bash
python3 code/compute_Y1.py \
  --mode pivotA_proof \
  --Y0 30000 \
  --C1 1e-3 \
  --prec 120 \
  --ln2_terms 40 \
  --mertens_ref "(use the exact reference string cited in the paper)" \
  --mertens_x0 55 \
  --mertens_B1 0.2614972128 \
  --mertens_c 1.0 \
  --nthprime_ref "(use the exact reference string cited in the paper)" \
  --nthprime_n0 6 \
  > certificates/appendixA/pivotA_proof_Y0=30000.txt

```
# Appendix A.4 — Small range 3 ≤ y < Y0 handled by exact tables

Appendix A.4 states that for primes \(3 \le y < Y_0\), the values `mreq(y)` are handled by a **finite,
independently checkable computation**, and the results are recorded as tables/transcript.

To make that statement concrete, this repository provides the canonical exact table:

## A3. `certificates/mreq/mreq_exact_3_to_30000_L50000000.txt`  (canonical exact table)

**What it contains.**  
A frozen file containing the exact certified values `mreq(y)` for the full range \(3 \le y \le 30000\),
computed with a large internal prime budget (`L50000000`).

**What it supports in Appendix A.4.**  
It is the concrete substitute for any “see tables appendix (??)” placeholder: it is the *actual table* a referee
can inspect and hash-verify.

**How to use it (no recomputation needed).**  
The intended referee workflow is the hash verification (`sha256sum -c manifest.sha256`).  
Recomputation is optional and may be expensive.

# Appendix C — Branch-and-bound certificate (transcript + summary)

Appendix C provides a referee-checkable finite certificate in the form of:

- `certificates/appendixC/transcript.jsonl` — the full auditable transcript of the BnB run
- `certificates/appendixC/summary.json` — the run summary (parameters + transcript SHA256)

**What it supports in Appendix C.**  
It makes the finite enumeration step independently checkable: the transcript can be replayed deterministically
by the shipped checker, and the repository hash manifest guarantees that the transcript/summary match the published artefacts.

**How to verify (no recomputation needed).**  
First run the repository-level hash check:

```bash
cd certificates
sha256sum -c manifest.sha256
```
Then replay-check the transcript:
```bash
python3 code/lehmer_bnb.py --mode check_transcript \
  --summary certificates/appendixC/summary.json
```

# Appendix D — Case B finite sanity scan (explicitly non-logical)

Appendix D is described in the paper as a finite scan used only for **sanity-checking** the explicit expressions
implemented in `compute_Y1.py`. The paper explicitly states that **no global “for all y ≥ …” statement** is deduced
from this scan; the global large-y exclusion comes from the analytic Case B argument.

Accordingly, only a single canonical scan output is included:

## D1. `certificates/appendixD/caseB_sanity_scan.txt`

**What it contains.**  
Representative scan output on a finite interval, recording the evaluated expressions and pass/fail conditions.

**What it supports in Appendix D.**  
A reproducible sanity check that the implemented explicit bounds behave as expected on the stated finite window.

**How to regenerate (optional; adjust interval to match the paper).**
```bash
python3 code/compute_Y1.py \
  --mode caseB \
  --y_min 3 --y_max 200 \
  --mreq_mode hybrid \
  --Y0 30000 --C1 1e-3 \
  --prime_limit 1000000 \
  > certificates/appendixD/caseB_sanity_scan.txt

```
## About `lehmer_bnb.py` (finite verification infrastructure)

`code/lehmer_bnb.py` is the “sieve + lock” engine:

- **Sieve mode (finite ground-truth check up to `Ny`)**  
  This mode performs a direct finite check on a bounded interval: it enumerates squarefree odd composites
  \(n \le Ny\) (subject to the y-range routing used in the paper) and tests Lehmer’s condition
  \(\varphi(n)\mid(n-1)\).  
  Conceptually, this is the “brute-force verifier on a finite window”.

- **Lock mode (support enumeration + pruning)**  
  This mode works at the level of supports \(S\) (finite sets of odd primes) and tracks
  \(n_S=\prod_{p\in S}p\) and \(L(S)=\mathrm{lcm}\{p-1:p\in S\}\).
  It explores a search tree of admissible extensions and applies pruning rules (budget caps, upper bounds for
  truncated Euler products, gcd/inheritance constraints, saturation-related filters).
  The output is an auditable per-\(y\) summary table reporting how many states were explored and which pruning
  channels fired.

**Why this matters for the paper.**  
The paper describes a “finite verification infrastructure” (Appendix C): the point is to make any finite
enumeration step independently checkable by shipping (i) the generating program, (ii) the resulting transcript(s),
and (iii) cryptographic hashes.  
`lehmer_bnb.py` is the generator side of that infrastructure.

## Hash policy

All frozen artefacts in `certificates/` are covered by:
- `certificates/manifest.sha256` (repository-level integrity check).

Some artefacts also embed a `sha256=...` line inside the file output to make tampering detectable when files are
copied out of the repository context.

## Repository layout

  compute_Y1.py
  lehmer_bnb.py

certificates/
  manifest.sha256
  appendixA/
    pivot_only_y3_200.txt
    pivotA_proof_Y0=30000.txt
  mreq/
    mreq_exact_3_to_30000_L50000000.txt
  caseB_scans/
    appB_caseB.txt

## License

Code is released under the MIT License (see `LICENSE`).

## Citation

Please cite the Zenodo record of the paper (DOI) which links back to this repository.

