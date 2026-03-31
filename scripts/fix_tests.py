"""Apply test fixes for construction refs and generic justification names."""

path = "verifier/tests/test_soundness.py"
with open(path, "r", encoding="utf-8") as f:
    c = f.read()

# Fix 6: test_two_constructions_yield_intersection
old6 = ('_line(2, "center(a, \\u03b1), on(b, \\u03b1)", "let-circle"),\n'
        '                _line(3, "center(b, \\u03b2), on(a, \\u03b2)", "let-circle"),\n'
        '                _line(4, "inside(a, \\u03b1)", "Diagrammatic"),\n'
        '                _line(5, "inside(b, \\u03b2)", "Diagrammatic"),')
new6 = ('_line(2, "center(a, \\u03b1), on(b, \\u03b1)", "let-circle", refs=[1]),\n'
        '                _line(3, "center(b, \\u03b2), on(a, \\u03b2)", "let-circle", refs=[1]),\n'
        '                _line(4, "inside(a, \\u03b1)", "Generality 3", refs=[2]),\n'
        '                _line(5, "inside(b, \\u03b2)", "Generality 3", refs=[3]),')
assert old6 in c, "Fix 6 not found"
c = c.replace(old6, new6, 1)
print("Fix 6 applied")

# Fix 6b: Intersection 5 line
old6b = '_line(6, "intersects(\\u03b1, \\u03b2)", "Diagrammatic"),'
new6b = '_line(6, "intersects(\\u03b1, \\u03b2)", "Intersection 5", refs=[2, 3, 4, 5]),'
assert old6b in c, "Fix 6b not found"
c = c.replace(old6b, new6b, 1)
print("Fix 6b applied")

# Fix 5: test_given_construction_diagrammatic_chain
old5 = ('_line(2, "center(a, \\u03b1), on(b, \\u03b1)", "let-circle"),\n'
        '                _line(3, "center(b, \\u03b2), on(a, \\u03b2)", "let-circle"),\n'
        '                # Both centers are inside their own circles\n'
        '                _line(4, "inside(a, \\u03b1)", "Diagrammatic"),\n'
        '                _line(5, "inside(b, \\u03b2)", "Diagrammatic"),')
new5 = ('_line(2, "center(a, \\u03b1), on(b, \\u03b1)", "let-circle", refs=[1]),\n'
        '                _line(3, "center(b, \\u03b2), on(a, \\u03b2)", "let-circle", refs=[1]),\n'
        '                # Both centers are inside their own circles\n'
        '                _line(4, "inside(a, \\u03b1)", "Generality 3", refs=[2]),\n'
        '                _line(5, "inside(b, \\u03b2)", "Generality 3", refs=[3]),')
assert old5 in c, "Fix 5 not found"
c = c.replace(old5, new5, 1)
print("Fix 5 applied")

# Fix 4: test_construction_to_diagrammatic_chain
old4 = ('_line(2, "center(a, \\u03b1), on(b, \\u03b1)", "let-circle"),\n'
        '                _line(3, "inside(a, \\u03b1)", "Diagrammatic"),')
new4 = ('_line(2, "center(a, \\u03b1), on(b, \\u03b1)", "let-circle", refs=[1]),\n'
        '                _line(3, "inside(a, \\u03b1)", "Generality 3", refs=[2]),')
assert old4 in c, "Fix 4 not found"
c = c.replace(old4, new4, 1)
print("Fix 4 applied")

# Fix 3: test_later_step_uses_earlier_construction
old3 = ('_line(2, "center(a, \\u03b1), on(b, \\u03b1)", "let-circle"),\n'
        '                # center(a,')
new3 = ('_line(2, "center(a, \\u03b1), on(b, \\u03b1)", "let-circle", refs=[1]),\n'
        '                # center(a,')
assert old3 in c, "Fix 3a not found"
c = c.replace(old3, new3, 1)
print("Fix 3a applied")

old3b = '_line(3, "inside(a, \\u03b1)", "Diagrammatic"),'
new3b = '_line(3, "inside(a, \\u03b1)", "Generality 3", refs=[2]),'
assert old3b in c, "Fix 3b not found"
c = c.replace(old3b, new3b, 1)
print("Fix 3b applied")

# Fix 2: test_let_line_accepted_with_distinctness
old2 = '_line(2, "on(a, L), on(b, L)", "let-line"),'
new2 = '_line(2, "on(a, L), on(b, L)", "let-line", refs=[1]),'
assert old2 in c, "Fix 2 not found"
c = c.replace(old2, new2, 1)
print("Fix 2 applied")

# Fix 1: test_let_circle_accepted_with_distinctness
old1 = ('_line(2, "center(a, \\u03b1), on(b, \\u03b1)", "let-circle"),\n'
        '            ],')
new1 = ('_line(2, "center(a, \\u03b1), on(b, \\u03b1)", "let-circle", refs=[1]),\n'
        '            ],')
assert old1 in c, "Fix 1 not found"
c = c.replace(old1, new1, 1)
print("Fix 1 applied")

with open(path, "w", encoding="utf-8") as f:
    f.write(c)
print("All fixes written to disk.")
