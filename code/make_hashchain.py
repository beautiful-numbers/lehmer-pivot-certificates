#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import argparse, hashlib, json
from pathlib import Path

ZERO64 = "0" * 64

def sha256_hex(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

def canonical_bytes(rec: dict) -> bytes:
    tmp = dict(rec)
    tmp.pop("hash", None)
    tmp.pop("_lineno", None)
    s = json.dumps(tmp, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return s.encode("utf-8")

def main() -> int:
    ap = argparse.ArgumentParser(description="Add prev_hash/hash chain to a JSONL transcript.")
    ap.add_argument("infile", type=Path)
    ap.add_argument("outfile", type=Path)
    args = ap.parse_args()

    prev = ZERO64
    n = 0

    with args.infile.open("r", encoding="utf-8") as fin, args.outfile.open("w", encoding="utf-8", newline="\n") as fout:
        for line in fin:
            s = line.strip()
            if not s or s.startswith("#"):
                continue
            rec = json.loads(s)
            if not isinstance(rec, dict):
                raise SystemExit("FAIL: expected JSON objects per line")

            rec["prev_hash"] = prev
            h = sha256_hex(canonical_bytes(rec))
            rec["hash"] = h

            fout.write(json.dumps(rec, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n")
            prev = h
            n += 1

    print(f"PASS: wrote {n} records with hash-chain")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
