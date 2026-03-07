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


def serialize_to_json(canvas_state: dict, journal_steps: List[dict],
                      metadata: Optional[dict] = None) -> str:
    output = {
        "format": "euclid-proof",
        "version": FILE_FORMAT["VERSION"],
        "program": FILE_FORMAT["PROGRAM"],
        "metadata": metadata or {},
        "canvas": {
            "points": canvas_state.get("points", []),
            "segments": canvas_state.get("segments", []),
            "circles": canvas_state.get("circles", []),
            "angleMarks": canvas_state.get("angle_marks", []),
        },
        "proof": {
            "steps": journal_steps,
        },
        "exportedAt": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    return json.dumps(output, indent=2, ensure_ascii=False)


def deserialize_from_json(text: str) -> dict:
    data = json.loads(text)
    canvas = data.get("canvas", {})
    proof = data.get("proof", {})
    return {
        "metadata": data.get("metadata", {}),
        "points": canvas.get("points", []),
        "segments": canvas.get("segments", []),
        "circles": canvas.get("circles", []),
        "angle_marks": canvas.get("angleMarks", []),
        "steps": proof.get("steps", []),
    }


def save_proof(path: str, canvas_state: dict, journal_steps: List[dict],
               metadata: Optional[dict] = None):
    text = serialize_to_json(canvas_state, journal_steps, metadata)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


def load_proof(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as f:
        return deserialize_from_json(f.read())
