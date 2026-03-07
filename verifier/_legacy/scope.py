"""
scope.py — Fitch-style scope tracking.

Rules:
  1. A line can only cite earlier lines.
  2. A line at depth d can cite lines at depth <= d in the same subproof.
  3. An Assume at the same depth as a prior line opens a new sibling
     subproof; lines in the prior sibling are no longer visible.
  4. When depth drops below d, lines at depth d are no longer visible.
"""
from __future__ import annotations
from typing import Dict, List, Optional
from .ast import ProofLine


class ScopeTracker:
    def __init__(self):
        self.lines: List[ProofLine] = []
        self.index: Dict[int, int] = {}

    def add_line(self, line: ProofLine):
        idx = len(self.lines)
        self.lines.append(line)
        self.index[line.id] = idx

    def get_line(self, line_id: int) -> Optional[ProofLine]:
        idx = self.index.get(line_id)
        return self.lines[idx] if idx is not None else None

    def is_visible(self, from_id: int, target_id: int) -> bool:
        if target_id not in self.index or from_id not in self.index:
            return False
        fi = self.index[from_id]
        ti = self.index[target_id]
        if ti >= fi:
            return False
        target_depth = self.lines[ti].depth
        from_depth = self.lines[fi].depth
        if target_depth > from_depth:
            return self._path_clean(ti, fi, target_depth)
        if target_depth > 0:
            return self._path_clean(ti, fi, target_depth)
        return True

    def _path_clean(self, ti: int, fi: int, depth: int) -> bool:
        for i in range(ti + 1, fi + 1):
            if self.lines[i].depth < depth:
                return False
            if (i < fi
                    and self.lines[i].depth == depth
                    and self.lines[i].justification == "Assume"):
                return False
        return True

    def is_in_subproof(self, line_id: int, assume_id: int) -> bool:
        if line_id not in self.index or assume_id not in self.index:
            return False
        ai = self.index[assume_id]
        li = self.index[line_id]
        if li <= ai:
            return False
        assume_depth = self.lines[ai].depth
        for i in range(ai + 1, li + 1):
            if self.lines[i].depth < assume_depth:
                return False
        return True
