#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
caseB_minimal_checker.py

Minimal transcript checker for Case B gate / routing discipline.

What this checker enforces (structural only; not the full Case B math):
  - A deterministic *state identity layer*:
        S_ref = H_support(S) when S is present,
        state_id = H_state(y, S_ref),
    and all “same state” constraints are interpreted as “same state_id”.

  - Unique gate decision per state:
        at most one of {caseB_gate_pass, caseB_gate_fail} per state_id.

  - Terminal-B discipline:
        caseB_terminal(state_id) requires a prior caseB_gate_pass(state_id)
        and must carry a saturation certificate field (cert_sat / sat_cert / saturation_cert).

  - Scarcity / Appendix E / Prop5.3 / Thm5.3 actions require Terminal-B:
        any record whose type matches the configured “scarcity family”
        is invalid unless a prior caseB_terminal(state_id) exists.

  - Off-gate non-closure + required routing (the “B-NG discharge”):
        if a state is saturated AND gate-fail, then:
          (a) it may not be closed by any Case B scarcity/closure action, and
          (b) the *next* record that references that same state_id must be
                - handoff_caseC(state_id) if 3 <= y < Y2
                - continue_exploration(state_id) otherwise.

  - Transition hygiene:
        handoff_caseC / continue_exploration must include parent_state_id,
        and we require parent_state_id == state_id (self-parent) for these routing records,
        matching the “handoff the same state” convention.

  - Handoff consumption:
        every handoff_caseC(state_id) must be matched somewhere later in the transcript by
        caseC_claim(state_id) and caseC_close(state_id).

This is intentionally permissive about unknown record types, similar to caseC_minimal_checker.py.
You can map your transcript's record names via CLI flags.

Run:
  python3 code/caseB_minimal_checker.py certificates/appendixD/routing_transcript.jsonl --Y2 30011

Exit:
  PASS (0) / FAIL (1)
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple


class CheckError(Exception):
    pass


# ---------------------------
# Hashing & canonicalization
# ---------------------------

def sha256_hex(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def normalize_support(S: List[int]) -> List[int]:
    if not isinstance(S, list) or len(S) == 0:
        raise CheckError("Support S must be a non-empty list[int]")
    S2 = sorted(int(x) for x in S)
    if len(S2) != len(set(S2)):
        raise CheckError(f"Support has duplicates: {S}")
    if any(p <= 2 or p % 2 == 0 for p in S2):
        raise CheckError(f"Support contains non-odd-prime entries: {S}")
    # NOTE: We do not primality-test here; transcript generation/checkers elsewhere may.
    return S2


def H_support(S: List[int]) -> str:
    """Canonical support hash (hex)."""
    S2 = normalize_support(S)
    # Deterministic decimal encoding, no leading zeros by construction of str(int)
    payload = "S|" + ",".join(str(p) for p in S2)
    return sha256_hex(payload.encode("utf-8"))


def H_state(y: int, S_ref_hex: str) -> str:
    """Canonical state hash (hex)."""
    payload = f"STATE|{int(y)}|{S_ref_hex.lower()}"
    return sha256_hex(payload.encode("utf-8"))


def as_hex(x) -> str:
    if isinstance(x, bytes):
        return x.hex()
    if isinstance(x, str):
        s = x.strip().lower()
        if s.startswith("0x"):
            s = s[2:]
        return s
    raise CheckError(f"Expected hex string/bytes, got {type(x)}")


# ---------------------------
# Record helpers
# ---------------------------

def rtype(rec: dict) -> str:
    t = rec.get("type") or rec.get("kind") or rec.get("tag")
    return str(t).strip().upper() if t is not None else ""


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

    # S_ref
    if "S_ref" in rec:
        S_ref = as_hex(rec["S_ref"])
    elif "support_ref" in rec:
        S_ref = as_hex(rec["support_ref"])
    elif "S" in rec:
        S_ref = H_support(rec["S"])
    else:
        raise CheckError("State-bearing record must include 'S' or 'S_ref'/'support_ref'")

    # state_id
    if "state_id" in rec:
        sid = as_hex(rec["state_id"])
    else:
        sid = H_state(y, S_ref)

    if strict_len:
        if len(S_ref) != 64:
            raise CheckError(f"S_ref must be 32-byte hex (64 chars), got len={len(S_ref)}")
        if len(sid) != 64:
            raise CheckError(f"state_id must be 32-byte hex (64 chars), got len={len(sid)}")

    expected_sid = H_state(y, S_ref)
    if sid.lower() != expected_sid.lower():
        raise CheckError(f"state_id mismatch: got {sid}, expected {expected_sid} for y={y}")

    if "S" in rec:
        expected_S_ref = H_support(rec["S"])
        if expected_S_ref.lower() != S_ref.lower():
            raise CheckError(f"S_ref mismatch: got {S_ref}, expected {expected_S_ref} for y={y}")

    return y, S_ref.lower(), sid.lower()


def get_parent_state_id(rec: dict, strict_len: bool) -> str:
    if "parent_state_id" not in rec:
        raise CheckError("Missing field 'parent_state_id' on transition record")
    pid = as_hex(rec["parent_state_id"]).lower()
    if strict_len and len(pid) != 64:
        raise CheckError(f"parent_state_id must be 32-byte hex (64 chars), got len={len(pid)}")
    return pid


@dataclass
class StateInfo:
    y: int
    S_ref: str
    gate_pass: bool = False
    gate_fail: bool = False
    terminal: bool = False
    # “Saturated” marker: either from terminal cert_sat or an explicit boolean flag
    is_saturated: bool = False


class CaseBMinimalChecker:
    def __init__(
        self,
        Y2: int,
        strict: bool = False,
        # record type mapping
        gate_pass_type: str = "CASEB_GATE_PASS",
        gate_fail_type: str = "CASEB_GATE_FAIL",
        terminal_type: str = "CASEB_TERMINAL",
        handoff_type: str = "HANDOFF_CASEC",
        continue_type: str = "CONTINUE_EXPLORATION",
        casec_claim_type: str = "CASEC_CLAIM",
        casec_close_type: str = "CASEC_CLOSE",
    ):
        self.Y2 = int(Y2)
        self.strict = strict

        self.T_GATE_PASS = gate_pass_type.upper()
        self.T_GATE_FAIL = gate_fail_type.upper()
        self.T_TERMINAL = terminal_type.upper()
        self.T_HANDOFF = handoff_type.upper()
        self.T_CONTINUE = continue_type.upper()
        self.T_CLAIM = casec_claim_type.upper()
        self.T_CLOSE = casec_close_type.upper()

        self.states: Dict[str, StateInfo] = {}

        # Handoff consumption tracking
        self.handoffs: Dict[str, int] = {}     # state_id -> y
        self.caseC_claim: Set[str] = set()
        self.caseC_close: Set[str] = set()

        # Terminal requirement family (hard-lock)
        self.REQUIRES_TERMINAL: Set[str] = {
            "APPENDIXE_APPLIED",
            "APPENDIXE_BOUND_APPLIED",
            "WITNESS_ACCOUNTING_APPLIED",
            "SCARCITY_CLOSED",
            "THM53_INVOKED",
            "PROP53_APPLIED",
            # aliases:
            "APPENDIXE_BOUND",
            "APPENDIXE",
            "THM5_3_INVOKED",
            "PROP5_3_APPLIED",
        }
        self.REQUIRES_TERMINAL_PREFIX = ("APPENDIXE", "WITNESS", "SCARCITY", "THM53", "PROP53")

        # Extra “closure-ish” names to forbid specifically on saturated gate-fail states
        self.FORBIDDEN_OFFGATE: Set[str] = {
            "CLOSED_BY_CASEB",
            "CASEB_CLOSED",
            "CASEB_CLOSE",
        }
        self.FORBIDDEN_OFFGATE_PREFIX = ("CLOSED", "CLOSE_BY_CASEB")

        # Required-next-step expectation for saturated gate-fail states:
        #   state_id -> expected_type (T_HANDOFF or T_CONTINUE)
        self.expect_next_for_state: Dict[str, str] = {}

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

    def _requires_terminal(self, t: str) -> bool:
        if t in self.REQUIRES_TERMINAL:
            return True
        return any(t.startswith(p) for p in self.REQUIRES_TERMINAL_PREFIX)

    def _forbidden_offgate(self, t: str) -> bool:
        if t in self.FORBIDDEN_OFFGATE:
            return True
        return any(t.startswith(p) for p in self.FORBIDDEN_OFFGATE_PREFIX)

    def _activate_required_routing_if_needed(self, sid: str, st: StateInfo) -> None:
        """
        If the state is saturated AND gate-fail, then enforce required routing on the *next*
        record that references this state_id.
        """
        if st.gate_fail and st.is_saturated:
            expected = self.T_HANDOFF if (3 <= st.y < self.Y2) else self.T_CONTINUE
            # If already active, keep the same expected value.
            if sid not in self.expect_next_for_state:
                self.expect_next_for_state[sid] = expected

    def check(self, path: Path) -> None:
        with path.open("r", encoding="utf-8") as f:
            for line_no, line in enumerate(f, start=1):
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                try:
                    rec = json.loads(line)
                except json.JSONDecodeError as e:
                    raise CheckError(f"{path}:{line_no}: invalid JSON: {e}")

                t = rtype(rec)
                if not t:
                    raise CheckError(f"{path}:{line_no}: missing record field 'type'/'kind'/'tag'")

                # Case C claim/close: accept minimal schema (state_id only).
                if t in (self.T_CLAIM, self.T_CLOSE):
                    if "state_id" not in rec:
                        raise CheckError(f"{path}:{line_no}: {t} missing state_id")
                    sid = as_hex(rec["state_id"]).lower()
                    if self.strict and len(sid) != 64:
                        raise CheckError(f"{path}:{line_no}: {t} state_id must be 64 hex chars")
                    if t == self.T_CLAIM:
                        self.caseC_claim.add(sid)
                    else:
                        self.caseC_close.add(sid)
                    continue

                # State-bearing records (and scarcity family)
                if t in (self.T_GATE_PASS, self.T_GATE_FAIL, self.T_TERMINAL, self.T_HANDOFF, self.T_CONTINUE) or self._requires_terminal(t) or self._forbidden_offgate(t):
                    y, S_ref, sid = get_state_fields(rec, strict_len=self.strict)
                    st = self._get_state(sid, y, S_ref)

                    # If there is a pending “next reference must be X”, check it *now*.
                    if sid in self.expect_next_for_state:
                        expected = self.expect_next_for_state[sid]
                        if t != expected:
                            raise CheckError(
                                f"{path}:{line_no}: required routing violated for saturated gate-fail state_id={sid}: "
                                f"expected next record type {expected}, got {t}"
                            )
                        # If it matches, consume the obligation (one-shot)
                        del self.expect_next_for_state[sid]
                        # Continue processing the record normally below.

                    # Gate pass/fail exclusivity + uniqueness
                    if t == self.T_GATE_PASS:
                        if st.gate_fail:
                            raise CheckError(f"{path}:{line_no}: gate_pass after gate_fail for state_id={sid}")
                        if st.gate_pass:
                            raise CheckError(f"{path}:{line_no}: duplicate gate_pass for state_id={sid}")
                        st.gate_pass = True
                        continue

                    if t == self.T_GATE_FAIL:
                        if st.gate_pass:
                            raise CheckError(f"{path}:{line_no}: gate_fail after gate_pass for state_id={sid}")
                        if st.gate_fail:
                            raise CheckError(f"{path}:{line_no}: duplicate gate_fail for state_id={sid}")
                        st.gate_fail = True
                        # If the record provides a saturation marker, activate routing immediately
                        if bool(rec.get("is_saturated", False)):
                            st.is_saturated = True
                        self._activate_required_routing_if_needed(sid, st)
                        continue

                    # Terminal-B
                    if t == self.T_TERMINAL:
                        if not st.gate_pass:
                            raise CheckError(f"{path}:{line_no}: caseB_terminal without prior gate_pass for state_id={sid}")
                        cert_sat = rec.get("cert_sat") or rec.get("sat_cert") or rec.get("saturation_cert")
                        if not cert_sat:
                            raise CheckError(f"{path}:{line_no}: caseB_terminal missing cert_sat for state_id={sid}")
                        st.is_saturated = True
                        st.terminal = True
                        # Terminal implies gate_pass already; OK.
                        continue

                    # Any scarcity/AppendixE/Prop53/Thm53-like action requires Terminal-B
                    if self._requires_terminal(t):
                        if not st.terminal:
                            raise CheckError(f"{path}:{line_no}: {t} requires prior caseB_terminal for state_id={sid}")
                        continue

                    # Off-gate closure forbidden on saturated gate-fail states
                    if self._forbidden_offgate(t):
                        if st.gate_fail and st.is_saturated:
                            raise CheckError(
                                f"{path}:{line_no}: forbidden Case B closure record {t} on saturated gate-fail state_id={sid}"
                            )
                        continue

                    # Routing transitions
                    if t == self.T_HANDOFF:
                        # Must be in covered range
                        if not (3 <= y < self.Y2):
                            raise CheckError(
                                f"{path}:{line_no}: handoff_caseC out of range y={y} (need 3<=y<Y2={self.Y2})"
                            )
                        # Must carry parent_state_id and be self-parented (handoff the same state)
                        pid = get_parent_state_id(rec, strict_len=self.strict)
                        if pid != sid:
                            raise CheckError(
                                f"{path}:{line_no}: handoff_caseC parent_state_id must equal state_id (self-parent). "
                                f"got parent_state_id={pid}, state_id={sid}"
                            )
                        if sid in self.handoffs:
                            raise CheckError(f"{path}:{line_no}: duplicate handoff_caseC for state_id={sid}")
                        self.handoffs[sid] = y
                        continue

                    if t == self.T_CONTINUE:
                        # Must carry parent_state_id and be self-parented (continue exploration on the same state)
                        pid = get_parent_state_id(rec, strict_len=self.strict)
                        if pid != sid:
                            raise CheckError(
                                f"{path}:{line_no}: continue_exploration parent_state_id must equal state_id (self-parent). "
                                f"got parent_state_id={pid}, state_id={sid}"
                            )

                        # Update saturation marker if provided
                        if bool(rec.get("is_saturated", False)):
                            st.is_saturated = True

                        # If we are saturated+gate_fail and y<Y2, continue is forbidden (must handoff).
                        if st.gate_fail and st.is_saturated and (3 <= y < self.Y2):
                            raise CheckError(
                                f"{path}:{line_no}: continue_exploration forbidden for saturated gate-fail in covered range "
                                f"(must handoff_caseC). state_id={sid}, y={y}"
                            )
                        # If we are saturated+gate_fail and y>=Y2, continue is allowed and is the required route.
                        continue

                # Otherwise: ignore record type.

                # However, a non-gate/sat record might still carry an explicit saturation marker for a gate-fail state.
                # We intentionally do not infer saturation from unrelated records to keep the checker minimal.

        # Post-checks:
        # (1) Every handoff must be claimed and closed
        for sid, y in self.handoffs.items():
            if sid not in self.caseC_claim:
                raise CheckError(f"Handoff not claimed in Case C block y={y}: state_id={sid}")
            if sid not in self.caseC_close:
                raise CheckError(f"Handoff not closed in Case C block y={y}: state_id={sid}")

        # (2) Any pending required routing is a failure (no “next reference” occurred)
        if self.expect_next_for_state:
            # report one example deterministically
            sid = next(iter(self.expect_next_for_state.keys()))
            exp = self.expect_next_for_state[sid]
            st = self.states.get(sid)
            y = st.y if st else "?"
            raise CheckError(
                f"Required routing not satisfied: saturated gate-fail state_id={sid} (y={y}) "
                f"expected next record type {exp}, but transcript ended (or never referenced state again)."
            )

        # (3) Sanity: no state both terminal and gate_fail (should be implied by rules)
        for sid, st in self.states.items():
            if st.gate_fail and st.terminal:
                raise CheckError(f"Invalid: state_id={sid} both gate_fail and terminal")


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description="Minimal checker for Case B gate / routing discipline (JSONL transcript).")
    ap.add_argument("transcript", type=Path, help="Path to JSONL transcript (combined Case B/C ok).")
    ap.add_argument("--Y2", type=int, required=True, help="Upper bound for Case C (extended) coverage: checks 3<=y<Y2.")
    ap.add_argument("--strict", action="store_true", help="Strict 32-byte hex length checks for hashes.")
    # record type mapping (for schema iterations)
    ap.add_argument("--gate-pass-type", default="caseB_gate_pass")
    ap.add_argument("--gate-fail-type", default="caseB_gate_fail")
    ap.add_argument("--terminal-type", default="caseB_terminal")
    ap.add_argument("--handoff-type", default="handoff_caseC")
    ap.add_argument("--continue-type", default="continue_exploration")
    ap.add_argument("--casec-claim-type", default="caseC_claim")
    ap.add_argument("--casec-close-type", default="caseC_close")
    args = ap.parse_args(argv)

    try:
        ck = CaseBMinimalChecker(
            Y2=args.Y2,
            strict=args.strict,
            gate_pass_type=args.gate_pass_type,
            gate_fail_type=args.gate_fail_type,
            terminal_type=args.terminal_type,
            handoff_type=args.handoff_type,
            continue_type=args.continue_type,
            casec_claim_type=args.casec_claim_type,
            casec_close_type=args.casec_close_type,
        )
        ck.check(args.transcript)
    except CheckError as e:
        print(f"FAIL: {e}", file=sys.stderr)
        return 1

    print("PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
