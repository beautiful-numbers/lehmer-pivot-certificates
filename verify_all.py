#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
verify_all.py

Deterministic verification runner for:
  https://github.com/beautiful-numbers/lehmer-pivot-certificates

This script is stdlib-only and cross-platform (Windows/Linux/macOS).

What it verifies (deterministically):
  (1) Integrity: recompute SHA256 for every entry listed in certificates/manifest.sha256.
  (2) Appendix C certificate package:
      (2a) summary/transcript SHA binding:
           certificates/appendixC/summary.json.transcript_sha256 ==
           SHA256(certificates/appendixC/transcript.jsonl bytes)
      (2b) COMPLETE COVERAGE (Appendix C transcript):
           - For every prime y in [y_min, y_max) from summary.json, there is exactly one Y_START(y)
             and exactly one Y_END(y), in properly nested order.
           - Each y-block is closed (Y_END occurs after its Y_START, with no interleaving).
           - All non-(Y_START/Y_END) records belong to the currently-open y-block and carry the same y.
  (3) Appendix D routing package:
      (3a) summary/transcript SHA binding for routing_summary.json / routing_transcript.jsonl.
      (3b) Run the structural routing discipline checker:
           python code/caseB_minimal_checker.py certificates/appendixD/routing_transcript.jsonl --Y2 <Y2>

Exit code:
  0 on success (prints PASS)
  1 on failure (prints FAIL + reason)

Usage:
  python verify_all.py
  python verify_all.py --Y2 30011
  python verify_all.py --repo-root .
  python verify_all.py --python python3
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Dict, Iterable, List, Tuple


# -----------------------
# Utilities
# -----------------------

def eprint(*args: object) -> None:
    print(*args, file=sys.stderr)


def sha256_file_bytes(path: Path, chunk_size: int = 1024 * 1024) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        while True:
            chunk = f.read(chunk_size)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def load_json(path: Path) -> Dict:
    try:
        with path.open("r", encoding="utf-8") as f:
            return json.load(f)
    except json.JSONDecodeError as e:
        raise RuntimeError(f"Invalid JSON: {path} ({e})")


def run_subprocess(cmd: List[str], cwd: Path) -> subprocess.CompletedProcess:
    env = dict(os.environ)
    # Determinism knobs (safe defaults)
    env.setdefault("PYTHONHASHSEED", "0")
    env.setdefault("LC_ALL", "C")
    env.setdefault("LANG", "C")
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )


# -----------------------
# Step 1: manifest verification
# -----------------------

def parse_manifest_lines(manifest_text: str, manifest_path: Path) -> List[Tuple[str, str]]:
    """
    Parse lines of the form:
      <64hex><2+spaces><relative/path>
    Ignores empty lines and comment lines starting with '#'.
    """
    out: List[Tuple[str, str]] = []
    for lineno, raw in enumerate(manifest_text.splitlines(), start=1):
        line = raw.strip("\n")
        if not line.strip():
            continue
        if line.lstrip().startswith("#"):
            continue

        # Prefer split on two spaces; fall back to whitespace.
        parts = line.split("  ", 1)
        if len(parts) == 2:
            sha, rel = parts[0].strip(), parts[1].strip()
        else:
            parts2 = line.split()
            if len(parts2) < 2:
                raise ValueError(f"{manifest_path}:{lineno}: cannot parse line: {raw!r}")
            sha = parts2[0].strip()
            rel = " ".join(parts2[1:]).strip()

        sha = sha.lower()
        if len(sha) != 64 or any(c not in "0123456789abcdef" for c in sha):
            raise ValueError(f"{manifest_path}:{lineno}: invalid sha256: {sha!r}")
        if not rel:
            raise ValueError(f"{manifest_path}:{lineno}: missing path")
        out.append((sha, rel))
    return out


def verify_manifest(repo_root: Path) -> int:
    manifest_path = repo_root / "certificates" / "manifest.sha256"
    if not manifest_path.exists():
        raise FileNotFoundError(f"Missing manifest: {manifest_path}")

    text = manifest_path.read_text(encoding="utf-8")
    entries = parse_manifest_lines(text, manifest_path)

    ok = 0
    fail = 0

    print("== Step 1: SHA256 integrity check ==")
    print(f"Manifest: {manifest_path}")

    for expected_sha, rel in entries:
        # Entries are relative to certificates/
        rel_norm = rel.replace("/", os.sep)
        file_path = repo_root / "certificates" / rel_norm
        if not file_path.exists():
            fail += 1
            print(f"FAIL   {rel} (missing)")
            continue

        actual_sha = sha256_file_bytes(file_path)
        if actual_sha == expected_sha:
            ok += 1
        else:
            fail += 1
            print(f"FAIL   {rel}")
            print(f"  expected: {expected_sha}")
            print(f"  got:      {actual_sha}")

    if fail:
        raise RuntimeError(f"Manifest check failed: {fail} FAIL / {ok} OK")

    print(f"PASS   ({ok} files verified)")
    return ok


# -----------------------
# Primes (for coverage)
# -----------------------

def primes_in_range(lo: int, hi: int) -> List[int]:
    """
    Return list of primes p with lo <= p < hi.
    Deterministic sieve (stdlib-only).
    """
    if hi <= 2 or hi <= lo:
        return []
    n = hi - 1
    sieve = bytearray(b"\x01") * (n + 1)
    if n >= 0:
        sieve[0:2] = b"\x00\x00"
    p = 2
    while p * p <= n:
        if sieve[p]:
            step = p
            start = p * p
            sieve[start:n + 1:step] = b"\x00" * (((n - start) // step) + 1)
        p += 1
    return [x for x in range(max(lo, 2), hi) if sieve[x]]


# -----------------------
# Step 2: Appendix C binding + completeness
# -----------------------

def verify_summary_transcript_binding(summary_path: Path, transcript_path: Path, label: str) -> Dict:
    """
    Checks summary.json exists, has transcript_sha256, and matches sha256(transcript bytes).
    Returns loaded summary dict (for further checks).
    """
    print(f"\n== {label}: summary/transcript SHA binding ==")
    if not summary_path.exists():
        raise FileNotFoundError(f"Missing summary: {summary_path}")
    if not transcript_path.exists():
        raise FileNotFoundError(f"Missing transcript: {transcript_path}")

    summary = load_json(summary_path)

    tool = summary.get("tool")
    mode = summary.get("mode")
    params = summary.get("params")
    tsha = summary.get("transcript_sha256")

    if not isinstance(tool, str) or not tool:
        raise RuntimeError(f"{summary_path}: missing/invalid 'tool'")
    if not isinstance(mode, str) or not mode:
        raise RuntimeError(f"{summary_path}: missing/invalid 'mode'")
    if not isinstance(params, dict):
        raise RuntimeError(f"{summary_path}: missing/invalid 'params'")
    if not isinstance(tsha, str) or len(tsha.strip().lower()) != 64:
        raise RuntimeError(f"{summary_path}: missing/invalid 'transcript_sha256'")

    expected = tsha.strip().lower()
    actual = sha256_file_bytes(transcript_path)

    print(f"tool: {tool}   mode: {mode}")
    if actual != expected:
        raise RuntimeError(
            f"Transcript SHA mismatch for {transcript_path}\n"
            f"  expected (summary): {expected}\n"
            f"  got (file sha256):  {actual}"
        )

    print("PASS")
    return summary


def iter_jsonl(path: Path) -> Iterable[Dict]:
    """
    Stream JSON objects from a .jsonl file.
    """
    with path.open("r", encoding="utf-8") as f:
        for lineno, line in enumerate(f, start=1):
            s = line.strip()
            if not s:
                continue
            try:
                obj = json.loads(s)
            except json.JSONDecodeError as e:
                raise RuntimeError(f"{path}:{lineno}: invalid JSON ({e})")
            if not isinstance(obj, dict):
                raise RuntimeError(f"{path}:{lineno}: expected JSON object")
            obj["_lineno"] = lineno  # for error messages (not used in hashing)
            yield obj


def verify_appendixC_completeness(summary: Dict, transcript_path: Path) -> None:
    """
    Proves (in the sense of deterministic checking) that Appendix C coverage is complete:

      - Exactly one Y_START and one Y_END per prime y in [y_min, y_max)
      - Proper block structure (no interleaving, every block closed)
      - Every record carries a y that matches the currently open block
    """
    print("\n== Step 2c (Appendix C): COMPLETE COVERAGE check ==")

    params = summary.get("params", {})
    y_min = params.get("y_min")
    y_max = params.get("y_max")

    if not isinstance(y_min, int) or not isinstance(y_max, int):
        raise RuntimeError("Appendix C summary.json: params.y_min/y_max must be integers")

    if y_min < 2 or y_max <= y_min:
        raise RuntimeError(f"Appendix C summary.json: invalid y-range y_min={y_min}, y_max={y_max}")

    expected_primes = primes_in_range(y_min, y_max)
    expected_set = set(expected_primes)

    # Track which y got a start/end
    started = set()
    ended = set()
    ordered_ended: List[int] = []

    current_y = None

    for rec in iter_jsonl(transcript_path):
        t = rec.get("type")
        y = rec.get("y")

        # All records must have type and y
        if not isinstance(t, str) or not t:
            raise RuntimeError(f"{transcript_path}:{rec['_lineno']}: missing/invalid 'type'")
        if not isinstance(y, int):
            raise RuntimeError(f"{transcript_path}:{rec['_lineno']}: missing/invalid 'y'")

        if t == "Y_START":
            if current_y is not None:
                raise RuntimeError(
                    f"{transcript_path}:{rec['_lineno']}: Y_START(y={y}) while block for y={current_y} still open"
                )
            if y not in expected_set:
                raise RuntimeError(
                    f"{transcript_path}:{rec['_lineno']}: Y_START(y={y}) not in expected prime set [{y_min},{y_max})"
                )
            if y in started:
                raise RuntimeError(f"{transcript_path}:{rec['_lineno']}: duplicate Y_START for y={y}")
            started.add(y)
            current_y = y

        elif t == "Y_END":
            if current_y is None:
                raise RuntimeError(f"{transcript_path}:{rec['_lineno']}: Y_END(y={y}) with no open block")
            if y != current_y:
                raise RuntimeError(
                    f"{transcript_path}:{rec['_lineno']}: Y_END(y={y}) does not match open block y={current_y}"
                )
            if y in ended:
                raise RuntimeError(f"{transcript_path}:{rec['_lineno']}: duplicate Y_END for y={y}")
            ended.add(y)
            ordered_ended.append(y)
            current_y = None

        else:
            # Any other record must belong to the currently open y-block and carry matching y
            if current_y is None:
                raise RuntimeError(
                    f"{transcript_path}:{rec['_lineno']}: record type={t} occurs outside any Y_START/Y_END block"
                )
            if y != current_y:
                raise RuntimeError(
                    f"{transcript_path}:{rec['_lineno']}: record type={t} has y={y} but open block y={current_y}"
                )

    if current_y is not None:
        raise RuntimeError(f"{transcript_path}: EOF reached but block for y={current_y} is still open (missing Y_END)")

    missing_starts = [p for p in expected_primes if p not in started]
    missing_ends = [p for p in expected_primes if p not in ended]

    extra_starts = sorted([y for y in started if y not in expected_set])
    extra_ends = sorted([y for y in ended if y not in expected_set])

    if missing_starts or missing_ends or extra_starts or extra_ends:
        msg = ["Appendix C completeness failure:"]
        if missing_starts:
            msg.append(f"  missing Y_START for {len(missing_starts)} primes (first few: {missing_starts[:10]})")
        if missing_ends:
            msg.append(f"  missing Y_END for {len(missing_ends)} primes (first few: {missing_ends[:10]})")
        if extra_starts:
            msg.append(f"  extra Y_START for non-expected y values: {extra_starts[:10]}")
        if extra_ends:
            msg.append(f"  extra Y_END for non-expected y values: {extra_ends[:10]}")
        raise RuntimeError("\n".join(msg))

    # Strong check: ordering must match increasing primes (typical transcript generation)
    if ordered_ended != expected_primes:
        # Not strictly necessary for "coverage", but flags strange ordering/interleaving.
        # We'll treat it as a failure to keep the checker strict and audit-friendly.
        raise RuntimeError(
            "Appendix C transcript closes primes in an unexpected order.\n"
            f"  expected first 10 primes: {expected_primes[:10]}\n"
            f"  got first 10 ended:       {ordered_ended[:10]}"
        )

    print(f"PASS   (complete coverage for {len(expected_primes)} primes y in [{y_min},{y_max}))")


# -----------------------
# Step 3: routing checker
# -----------------------

def verify_routing_checker(repo_root: Path, python_exe: str, y2: int) -> None:
    """
    Runs code/caseB_minimal_checker.py on certificates/appendixD/routing_transcript.jsonl.
    Requires exit code 0 and "PASS" in stdout.
    """
    print("\n== Step 3: Appendix D routing discipline check ==")
    checker = repo_root / "code" / "caseB_minimal_checker.py"
    transcript = repo_root / "certificates" / "appendixD" / "routing_transcript.jsonl"

    if not checker.exists():
        raise FileNotFoundError(f"Missing routing checker: {checker}")
    if not transcript.exists():
        raise FileNotFoundError(f"Missing routing transcript: {transcript}")

    cmd = [python_exe, str(checker), str(transcript), "--Y2", str(y2)]
    cp = run_subprocess(cmd, cwd=repo_root)

    # Print stdout (useful for logs); stderr only on failure.
    sys.stdout.write(cp.stdout)

    if cp.returncode != 0:
        eprint(cp.stderr)
        raise RuntimeError(f"Routing checker failed (exit code {cp.returncode})")

    if "PASS" not in cp.stdout:
        eprint(cp.stderr)
        raise RuntimeError("Routing checker did not print PASS (unexpected output)")

    print("PASS")


# -----------------------
# Main
# -----------------------

def main() -> int:
    ap = argparse.ArgumentParser(
        description="Deterministic verifier: manifest + Appendix C completeness + routing checker."
    )
    ap.add_argument("--repo-root", default=".", help="Path to repo root (default: current directory).")
    ap.add_argument("--python", default=sys.executable, help="Python executable to use (default: current interpreter).")
    ap.add_argument("--Y2", type=int, default=30011, help="Y2 bound for routing checker (default: 30011).")
    args = ap.parse_args()

    repo_root = Path(args.repo_root).resolve()

    if not (repo_root / "certificates").is_dir():
        eprint(f"ERROR: {repo_root} does not look like a repo root (missing certificates/).")
        return 2
    if not (repo_root / "code").is_dir():
        eprint(f"ERROR: {repo_root} does not look like a repo root (missing code/).")
        return 2

    try:
        verify_manifest(repo_root)

        # Appendix C binding + completeness
        summary_c = verify_summary_transcript_binding(
            summary_path=repo_root / "certificates" / "appendixC" / "summary.json",
            transcript_path=repo_root / "certificates" / "appendixC" / "transcript.jsonl",
            label="Step 2 (Appendix C)",
        )
        verify_appendixC_completeness(
            summary=summary_c,
            transcript_path=repo_root / "certificates" / "appendixC" / "transcript.jsonl",
        )

        # Appendix D routing binding
        verify_summary_transcript_binding(
            summary_path=repo_root / "certificates" / "appendixD" / "routing_summary.json",
            transcript_path=repo_root / "certificates" / "appendixD" / "routing_transcript.jsonl",
            label="Step 2b (Appendix D routing)",
        )

        # Appendix D routing structural discipline
        verify_routing_checker(repo_root, args.python, args.Y2)

    except Exception as ex:
        eprint("\nFAIL:", ex)
        return 1

    print("\nPASS: all checks succeeded.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
