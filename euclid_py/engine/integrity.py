"""
Integrity — HMAC-SHA256 tamper detection for .euclid files.

Computes a hash over the locked fields (premises, goal,
declarations, difficulty, hints, locked_features) while excluding
editable content (proof steps, canvas).  When a locked file is
exported the hash is stored in ``metadata.integrity_hash``.
On load, if the hash is present, it is re-verified — if it mismatches the
file was tampered with and feature locks are not enforced.
"""
from __future__ import annotations

import hashlib
import hmac
import json
from typing import Any, Dict, List, Optional

# A fixed application key — provides tamper *detection* (not secrecy).
# Anyone could read the source, but the goal is to prevent accidental
# or casual modification, not defeat a determined attacker.
_APP_KEY = b"euclid-proof-system-v1-integrity"


def _canonical_payload(proof_section: dict, metadata: dict) -> bytes:
    """Build a deterministic JSON payload from locked fields."""
    payload = {
        "premises": proof_section.get("premises", []),
        "goal": proof_section.get("goal", ""),
        "declarations": proof_section.get("declarations", {}),
        "difficulty": metadata.get("difficulty", 1),
        "hints": metadata.get("hints", []),
        "locked_features": metadata.get("locked_features", {}),
    }
    return json.dumps(payload, sort_keys=True, ensure_ascii=True).encode("utf-8")


def compute_integrity_hash(proof_section: dict, metadata: dict) -> str:
    """Return the HMAC-SHA256 hex digest for the given proof + metadata."""
    payload = _canonical_payload(proof_section, metadata)
    return hmac.new(_APP_KEY, payload, hashlib.sha256).hexdigest()


def verify_integrity_hash(proof_section: dict, metadata: dict) -> bool:
    """Check whether the stored integrity_hash matches the computed one.

    Returns ``True`` if the hash is valid **or** if no hash is present
    (i.e. the file was not exported as locked).  Returns ``False``
    only when a hash exists but does not match (tampered).
    """
    stored = metadata.get("integrity_hash", "")
    if not stored:
        return True  # no lock → always valid
    expected = compute_integrity_hash(proof_section, metadata)
    return hmac.compare_digest(stored, expected)


# ── Lock feature constants ────────────────────────────────────────────
# Each key maps to a human-readable label shown in the Advanced
# settings tab.  The values are booleans (True = feature is locked).

LOCKABLE_FEATURES = {
    "hide_hints": "Hide hints",
    "disable_rule_reference": "Disable rule reference panel",
    "hide_difficulty": "Hide difficulty rating",
    "restrict_save": "Prevent saving over the original file",
    "lock_goal": "Lock goal (prevent editing the goal field)",
    "lock_premises": "Lock premises (prevent editing or adding premises)",
    "disable_lemma_change": "Disable loading lemmas",
    "disable_construction_tool": "Disable construction tool",
}

DEFAULT_LOCKS: Dict[str, bool] = {k: False for k in LOCKABLE_FEATURES}
