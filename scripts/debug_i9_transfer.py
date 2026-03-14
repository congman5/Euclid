"""Debug Angle transfer 9 (DA4) for I.9 line 22.

Line 22: [Angle transfer 9] refs=[4, 5, 6, 7, 14, 12, 21]
  -> ∠bae = ∠cae

We need to figure out what Angle transfer 9 actually means and whether
the transfer engine can derive it from the known context.
"""
import json, sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
from verifier.e_parser import parse_literal_list
from verifier.e_ast import Sort, Literal, SameSide, On, Between, Equals, AngleTerm
from verifier.e_transfer import TransferEngine
from verifier.e_consequence import ConsequenceEngine
from verifier.e_axioms import ALL_DIAGRAMMATIC_AXIOMS, ALL_TRANSFER_AXIOMS

sort_ctx = {}

# Known facts up to line 21 in Prop.I.9:
# Premises:
known_strs = [
    "¬(a = b)", "¬(a = c)", "¬(b = c)",
    "on(a, M)", "on(b, M)", "on(a, N)", "on(c, N)",
    "same-side(c, b, M)", "same-side(b, c, N)",
    # Line 10: let-circle
    "center(a, α)", "on(b, α)",
    # Line 11: Generality 3
    "inside(a, α)",
    # Line 12: let-point-on-line -> d on N and α
    "on(d, N)",  # d is on N... but the construction also puts d on α?
    # Actually line 12 says "on(d, α), on(d, N)" — this seems wrong for let-point-on-line
    # let-point-on-line gives on(d, L) for some line. If it's on N, that's one conclusion.
    # But on(d, α) is a circle... let me check
]

# Wait — looking at the proof dump:
# 12. [let-point-on-line] refs=[6] -> on(d, α), on(d, N)
# This doesn't make sense. let-point-on-line gives on(point, line). 
# α is a circle. This looks like a bug in the proof.

# Actually, let me re-read the construction rules.
# let-point-on-line: new_vars=[("a", POINT)], conclusion_pattern=[On("a", "L")]
# So it gives on(d, N) only (one line). The on(d, α) part is wrong.

# Let me check what the proof actually intends:
# The idea is to find point d on ray N from a, at distance ab from a.
# Then d should be on circle α (centered at a through b).
# The right construction would be: 
#   - let-intersection-circle-line-one or similar to get d on both N and α

# But the proof says let-point-on-line → on(d, α), on(d, N)
# This is mixing a line and circle in one point-on-line construction.

# Let me check if the verifier accepts this as-is or rejects it...
print("The issue is that I.9 line 12 uses let-point-on-line to claim")
print("on(d, α) and on(d, N), but α is a circle, not a line.")
print("let-point-on-line only gives on(point, line).")
print()
print("Similarly line 14 uses let-point-on-line for on(f, α), on(f, M)")
print("where α is also a circle.")
print()
print("These should use a circle-line intersection construction:")
print("  1. Establish intersects(α, N)")
print("  2. let-intersection-circle-line-one → on(d, α), on(d, N)")
print()
print("Or the proof should use let-point-on-circle + Segment transfer 4")
print("to establish the equal-distance property.")
