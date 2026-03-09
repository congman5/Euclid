"""
File Format — ported from fileFormat.js

Handles saving/loading .euclid proof files in JSON format.
"""
from __future__ import annotations

import json
import time
from dataclasses import asdict, dataclass, field
from typing import Any, Dict, List, Optional


FILE_FORMAT = {
    "VERSION": "1.0.0",
    "PROGRAM": "Euclid Elements Simulator (Python)",
    "EXTENSION": ".euclid",
}


def serialize_to_json(canvas_state: dict, journal_state: Optional[dict] = None,
                      metadata: Optional[dict] = None) -> str:
    output = {
        "format": "euclid-proof",
        "version": FILE_FORMAT["VERSION"],
        "program": FILE_FORMAT["PROGRAM"],
        "metadata": metadata or {},
        "canvas": {
            "points": canvas_state.get("points", []),
            "segments": canvas_state.get("segments", []),
            "rays": canvas_state.get("rays", []),
            "circles": canvas_state.get("circles", []),
            "angleMarks": canvas_state.get("angle_marks", []),
            "equalityGroups": canvas_state.get("equality_groups", []),
        },
        "exportedAt": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    if journal_state is not None:
        output["proof"] = {
            "name": journal_state.get("name", ""),
            "premises": journal_state.get("premises", []),
            "goal": journal_state.get("goal", ""),
            "declarations": journal_state.get("declarations", {}),
            "steps": journal_state.get("steps", []),
        }
    return json.dumps(output, indent=2, ensure_ascii=False)


def deserialize_from_json(text: str) -> dict:
    data = json.loads(text)
    canvas = data.get("canvas", {})
    proof = data.get("proof", None)
    result = {
        "metadata": data.get("metadata", {}),
        "points": canvas.get("points", []),
        "segments": canvas.get("segments", []),
        "rays": canvas.get("rays", []),
        "circles": canvas.get("circles", []),
        "angle_marks": canvas.get("angleMarks", []),
        "equality_groups": canvas.get("equalityGroups", []),
        "has_journal": proof is not None,
    }
    if proof is not None:
        result["journal"] = {
            "name": proof.get("name", ""),
            "premises": proof.get("premises", []),
            "goal": proof.get("goal", ""),
            "declarations": proof.get("declarations", {}),
            "steps": proof.get("steps", []),
        }
    return result


def save_proof(path: str, canvas_state: dict, journal_state: Optional[dict] = None,
               metadata: Optional[dict] = None):
    text = serialize_to_json(canvas_state, journal_state, metadata)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


def load_proof(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as f:
        return deserialize_from_json(f.read())


# ── Proof-only .euclid ───────────────────────────────────────────

def save_journal_json(path: str, journal_state: dict):
    """Save only the proof journal (no canvas) as a .euclid file."""
    output = {
        "format": "euclid-journal",
        "version": FILE_FORMAT["VERSION"],
        "program": FILE_FORMAT["PROGRAM"],
        "proof": {
            "name": journal_state.get("name", ""),
            "premises": journal_state.get("premises", []),
            "goal": journal_state.get("goal", ""),
            "declarations": journal_state.get("declarations", {}),
            "steps": journal_state.get("steps", []),
        },
        "exportedAt": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    with open(path, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2, ensure_ascii=False)


def load_journal_json(path: str) -> dict:
    """Load a proof-only .euclid file and return a journal state dict."""
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)
    proof = data.get("proof", {})
    return {
        "name": proof.get("name", ""),
        "premises": proof.get("premises", []),
        "goal": proof.get("goal", ""),
        "declarations": proof.get("declarations", {}),
        "steps": proof.get("steps", []),
    }


def detect_file_format(path: str) -> str:
    """Return 'euclid-proof', 'euclid-journal', or 'unknown'."""
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        fmt = data.get("format", "")
        if fmt in ("euclid-proof", "euclid-journal"):
            return fmt
        # Heuristic: has canvas → world file; has proof only → journal
        if "canvas" in data:
            return "euclid-proof"
        if "proof" in data:
            return "euclid-journal"
    except Exception:
        pass
    return "unknown"
