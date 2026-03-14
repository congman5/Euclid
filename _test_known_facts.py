"""Test: autofill uses all known facts like the verifier does."""
import os, sys
os.environ['QT_QPA_PLATFORM'] = 'offscreen'
from PyQt6.QtWidgets import QApplication
app = QApplication(sys.argv)

from euclid_py.engine.proposition_data import get_proposition
from euclid_py.ui.main_window import MainWindow

w = MainWindow()
pp = w._workspace._proof_panel

# Test 1: let-circle with no refs — premise ¬(a=b) should be found from known facts
print("=== Test 1: let-circle with no refs (prereq from premise) ===")
p = get_proposition('euclid-I.1')
w.open_proposition(p)
pp.add_step('', 'let-circle', [])   # no refs, but ¬(a=b) is in premise
pp._eval_all()
for s in pp._steps:
    print(f"  Step {s.line_number}: text={s.text!r} just={s.justification!r} status={s.status!r}")

# Test 2: Two let-circles — second should get β
print("\n=== Test 2: Two let-circles, second gets fresh β ===")
pp.clear()
p = get_proposition('euclid-I.1')
w.open_proposition(p)
pp.add_step('', 'let-circle', [])
pp.add_step('', 'let-circle', [])
pp._eval_all()
for s in pp._steps:
    print(f"  Step {s.line_number}: text={s.text!r} just={s.justification!r} status={s.status!r}")
assert '\u03b1' in pp._steps[0].text, "Step 2 should use \u03b1"
assert '\u03b2' in pp._steps[1].text, "Step 3 should use \u03b2"

# Test 3: Generality 3 with no refs — prereq center(a,α) from prior step
print("\n=== Test 3: Generality 3, no refs (prereq from prior step) ===")
pp.clear()
p = get_proposition('euclid-I.1')
w.open_proposition(p)
pp.add_step('center(a,\u03b1), on(b,\u03b1)', 'let-circle', [1])
pp.add_step('', 'Generality 3', [])  # no refs, but center(a,α) is known
pp._eval_all()
for s in pp._steps:
    print(f"  Step {s.line_number}: text={s.text!r} just={s.justification!r} status={s.status!r}")
assert 'inside' in pp._steps[1].text, "Generality 3 should produce inside(a,α)"

# Test 4: Full Prop I.1 chain with no refs
print("\n=== Test 4: Full chain with explicit refs ===")
pp.clear()
p = get_proposition('euclid-I.1')
w.open_proposition(p)
pp.add_step('', 'let-circle', [1])
pp.add_step('', 'let-circle', [1])
pp.add_step('', 'Generality 3', [2])
pp.add_step('', 'Generality 3', [3])
pp._eval_all()
for s in pp._steps:
    print(f"  Step {s.line_number}: text={s.text!r} just={s.justification!r} status={s.status!r}")

# Test 5: Segment transfer with known facts from prior steps
print("\n=== Test 5: Segment transfer 4, refs to circle+intersection steps ===")
pp.clear()
p = get_proposition('euclid-I.1')
w.open_proposition(p)
pp.add_step('center(a,\u03b1), on(b,\u03b1)', 'let-circle', [1])
pp.add_step('center(b,\u03b2), on(a,\u03b2)', 'let-circle', [1])
pp.add_step('intersects(\u03b1,\u03b2)', 'Diagrammatic', [])
pp.add_step('on(c,\u03b1), on(c,\u03b2)', 'let-intersection-circle-circle-two', [4])
pp.add_step('', 'Segment transfer 4', [2, 5])
pp._eval_all()
for s in pp._steps:
    print(f"  Step {s.line_number}: text={s.text!r} just={s.justification!r} status={s.status!r}")

# Test 6: Load Proposition I.1.euclid — must still work
print("\n=== Test 6: Load Proposition I.1.euclid ===")
pp.clear()
from euclid_py.engine.file_format import load_proof
data = load_proof('solved_proofs/Proposition I.1.euclid')
pp.restore_journal_state(data["journal"])
pp._eval_all()
tip = pp._goal_status.toolTip()
print(f"  Tooltip: {tip[:80]}")
for s in pp._steps:
    print(f"  Step {s.line_number}: text={s.text!r} status={s.status!r}")

print("\nDONE")
