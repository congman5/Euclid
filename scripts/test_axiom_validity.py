"""
Exhaustive geometric verification of the proposed axiom:

  between(d,a,c) ∧ on(d,K) ∧ on(f,K) ∧ ¬on(a,K) ∧ ¬ss(e,a,K)
  ∧ ¬on(e,K) ∧ on(a,M) ∧ on(f,M) ∧ ¬on(d,M) ∧ ¬on(e,M)
  → ¬ss(e,d,M)

We test this with thousands of random configurations in coordinate geometry.
A point p is on the same side of line L as point q iff:
  sign(cross(L_dir, p - L_point)) == sign(cross(L_dir, q - L_point))

"between(d,a,c)" means a is strictly between d and c on a line.
"""

import math
import random
import sys

random.seed(42)

def cross2d(u, v):
    """2D cross product (scalar)."""
    return u[0]*v[1] - u[1]*v[0]

def vadd(a, b):
    return (a[0]+b[0], a[1]+b[1])

def vsub(a, b):
    return (a[0]-b[0], a[1]-b[1])

def vscale(s, v):
    return (s*v[0], s*v[1])

def vnorm(v):
    return math.sqrt(v[0]**2 + v[1]**2)

def vdot(a, b):
    return a[0]*b[0] + a[1]*b[1]

def vnormalize(v):
    n = vnorm(v)
    return (v[0]/n, v[1]/n)

def randn2():
    """Random 2D point from normal distribution."""
    import random as _r
    return (_r.gauss(0,1), _r.gauss(0,1))

def side_of_line(point, line_p1, line_p2):
    d = vsub(line_p2, line_p1)
    v = vsub(point, line_p1)
    c = cross2d(d, v)
    if abs(c) < 1e-10:
        return 0
    return 1 if c > 0 else -1

def same_side(p, q, line_p1, line_p2):
    sp = side_of_line(p, line_p1, line_p2)
    sq = side_of_line(q, line_p1, line_p2)
    if sp == 0 or sq == 0:
        return None
    return sp == sq

def is_between(d, a, c):
    dc = vsub(c, d)
    if vnorm(dc) < 1e-12:
        return False
    da = vsub(a, d)
    if abs(cross2d(dc, da)) > 1e-8:
        return False
    t = vdot(da, dc) / vdot(dc, dc)
    return 0 < t < 1

def on_line(p, l1, l2):
    d = vsub(l2, l1)
    v = vsub(p, l1)
    return abs(cross2d(d, v)) < 1e-8

def test_axiom(n_tests=500000):
    """Test the proposed axiom with random configurations."""

    violations = 0
    valid_tests = 0

    for _ in range(n_tests):
        a = vscale(5, randn2())

        direction = vnormalize(randn2())
        t1 = random.uniform(0.5, 5.0)
        t2 = random.uniform(0.5, 5.0)
        d = vsub(a, vscale(t1, direction))
        c = vadd(a, vscale(t2, direction))

        assert is_between(d, a, c), "a should be between d and c"

        f_dir = randn2()
        while abs(cross2d(direction, f_dir)) < 0.1:
            f_dir = randn2()
        f_dist = random.uniform(0.5, 5.0)
        f = vadd(a, vscale(f_dist, f_dir))

        if on_line(a, d, f):
            continue
        if on_line(d, a, f):
            continue

        e = vscale(5, randn2())

        if on_line(e, d, f):
            continue
        if on_line(e, a, f):
            continue

        ss_ea_K = same_side(e, a, d, f)
        if ss_ea_K is None or ss_ea_K:
            continue

        valid_tests += 1

        ss_ed_M = same_side(e, d, a, f)
        if ss_ed_M is None:
            continue

        if ss_ed_M:
            violations += 1
            if violations <= 5:
                print(f"\nVIOLATION #{violations}:")
                print(f"  a={a}, d={d}, c={c}, f={f}, e={e}")
                print(f"  between(d,a,c): {is_between(d,a,c)}")
                print(f"  on(a,K=line(d,f)): {on_line(a,d,f)}")
                print(f"  on(e,K): {on_line(e,d,f)}")
                print(f"  on(e,M=line(a,f)): {on_line(e,a,f)}")
                print(f"  on(d,M): {on_line(d,a,f)}")
                print(f"  ss(e,a,K): {same_side(e,a,d,f)}")
                print(f"  ss(e,d,M): {same_side(e,d,a,f)} <- should be False!")

    print(f"\n{'='*60}")
    print(f"AXIOM TEST 1 (full version):")
    print(f"  between(d,a,c) ∧ on(d,K) ∧ on(f,K) ∧ ¬on(a,K)")
    print(f"  ∧ ¬ss(e,a,K) ∧ ¬on(e,K) ∧ on(a,M) ∧ on(f,M)")
    print(f"  ∧ ¬on(d,M) ∧ ¬on(e,M) → ¬ss(e,d,M)")
    print(f"  Valid tests: {valid_tests}")
    print(f"  Violations:  {violations}")
    print(f"  Result:      {'PASS ✓' if violations == 0 else 'FAIL ✗'}")

    return violations == 0

def test_simpler_axiom(n_tests=500000):
    """
    Test a SIMPLER version that doesn't need between(d,a,c):

    on(d,K) ∧ on(f,K) ∧ on(a,M) ∧ on(f,M) ∧ ¬on(a,K) ∧ ¬on(d,M)
    ∧ ¬ss(e,a,K) ∧ ¬on(e,K) ∧ ¬on(e,M) → ¬ss(e,d,M)
    """

    violations = 0
    valid_tests = 0

    for _ in range(n_tests):
        f = vscale(5, randn2())

        k_dir = vnormalize(randn2())
        m_dir = randn2()
        m_dir_n = vnorm(m_dir)
        if m_dir_n < 0.01:
            continue
        m_dir = (m_dir[0]/m_dir_n, m_dir[1]/m_dir_n)

        if abs(cross2d(k_dir, m_dir)) < 0.1:
            continue

        td = random.uniform(0.5, 5.0) * random.choice([-1, 1])
        d = vadd(f, vscale(td, k_dir))

        ta = random.uniform(0.5, 5.0) * random.choice([-1, 1])
        a = vadd(f, vscale(ta, m_dir))

        if on_line(a, d, f):
            continue
        if on_line(d, a, f):
            continue

        e = vscale(5, randn2())

        if on_line(e, d, f):
            continue
        if on_line(e, a, f):
            continue

        ss_ea_K = same_side(e, a, d, f)
        if ss_ea_K is None or ss_ea_K:
            continue

        valid_tests += 1

        ss_ed_M = same_side(e, d, a, f)
        if ss_ed_M is None:
            continue

        if ss_ed_M:
            violations += 1
            if violations <= 5:
                print(f"\nVIOLATION #{violations}:")
                print(f"  f={f}, d={d}, a={a}, e={e}")
                print(f"  K=line(d,f), M=line(a,f)")
                print(f"  ss(e,a,K): {same_side(e,a,d,f)}")
                print(f"  ss(e,d,M): {same_side(e,d,a,f)} <- should be False!")

    print(f"\n{'='*60}")
    print(f"AXIOM TEST 2 (simpler, no between):")
    print(f"  on(d,K) ∧ on(f,K) ∧ on(a,M) ∧ on(f,M) ∧ ¬on(a,K)")
    print(f"  ∧ ¬on(d,M) ∧ ¬ss(e,a,K) ∧ ¬on(e,K) ∧ ¬on(e,M)")
    print(f"  → ¬ss(e,d,M)")
    print(f"  Valid tests: {valid_tests}")
    print(f"  Violations:  {violations}")
    print(f"  Result:      {'PASS ✓' if violations == 0 else 'FAIL ✗'}")

    return violations == 0


def test_even_simpler(n_tests=500000):
    """
    Even simpler: two lines through a common point.

    on(a,L) ∧ on(a,M) ∧ on(b,L) ∧ on(c,M) ∧ ¬on(b,M) ∧ ¬on(c,L)
    ∧ ¬on(e,L) ∧ ¬on(e,M) ∧ ¬ss(e,b,M) → ¬ss(e,c,L)
    """

    violations = 0
    valid_tests = 0

    for _ in range(n_tests):
        a = vscale(3, randn2())

        l_dir = vnormalize(randn2())
        m_dir = vnormalize(randn2())
        if abs(cross2d(l_dir, m_dir)) < 0.1:
            continue

        tb = random.uniform(0.5, 5.0) * random.choice([-1, 1])
        b = vadd(a, vscale(tb, l_dir))

        tc = random.uniform(0.5, 5.0) * random.choice([-1, 1])
        c = vadd(a, vscale(tc, m_dir))

        if on_line(b, a, c):
            continue
        if on_line(c, a, b):
            continue

        e = vscale(5, randn2())

        if on_line(e, a, b):
            continue
        if on_line(e, a, c):
            continue

        ss_eb_M = same_side(e, b, a, c)
        if ss_eb_M is None or ss_eb_M:
            continue

        valid_tests += 1

        ss_ec_L = same_side(e, c, a, b)
        if ss_ec_L is None:
            continue

        if ss_ec_L:
            violations += 1
            if violations <= 3:
                print(f"\nVIOLATION #{violations}:")
                print(f"  a={a}, b={b}, c={c}, e={e}")

    print(f"\n{'='*60}")
    print(f"AXIOM TEST 3 (two lines through a, NO extra constraints):")
    print(f"  on(a,L) ∧ on(a,M) ∧ on(b,L) ∧ on(c,M)")
    print(f"  ∧ ¬on(b,M) ∧ ¬on(c,L) ∧ ¬on(e,L) ∧ ¬on(e,M)")
    print(f"  ∧ ¬ss(e,b,M) → ¬ss(e,c,L)")
    print(f"  Valid tests: {valid_tests}")
    print(f"  Violations:  {violations}")
    print(f"  Result:      {'PASS ✓' if violations == 0 else 'FAIL ✗'}")

    return violations == 0


def test_axiom_with_between_and_f(n_tests=500000):
    """
    between(d,a,c) ∧ between(f,a,b) 
    ∧ on(d,K) ∧ on(f,K) ∧ ¬on(a,K)
    ∧ ¬ss(e,a,K) ∧ ¬on(e,K)
    ∧ on(a,M) ∧ on(f,M) ∧ ¬on(d,M) ∧ ¬on(e,M)
    → ¬ss(e,d,M)
    """

    violations = 0
    valid_tests = 0

    for _ in range(n_tests):
        a = vscale(3, randn2())

        dir1 = vnormalize(randn2())
        dir2 = vnormalize(randn2())

        if abs(cross2d(dir1, dir2)) < 0.1:
            continue

        tb = random.uniform(1, 5)
        tc = random.uniform(1, 5)
        b = vadd(a, vscale(tb, dir1))
        c = vadd(a, vscale(tc, dir2))

        td = random.uniform(0.5, 5)
        d = vsub(a, vscale(td, dir2))

        tf = random.uniform(0.5, 5)
        f = vsub(a, vscale(tf, dir1))

        assert is_between(d, a, c)
        assert is_between(f, a, b)

        if on_line(a, d, f):
            continue
        if on_line(d, a, f):
            continue

        e = vscale(5, randn2())

        if on_line(e, d, f):
            continue
        if on_line(e, a, f):
            continue

        ss_ea_K = same_side(e, a, d, f)
        if ss_ea_K is None or ss_ea_K:
            continue

        valid_tests += 1

        ss_ed_M = same_side(e, d, a, f)
        if ss_ed_M is None:
            continue

        if ss_ed_M:
            violations += 1
            if violations <= 5:
                print(f"\nVIOLATION #{violations}:")
                print(f"  a={a}, b={b}, c={c}, d={d}, f={f}, e={e}")
                print(f"  between(d,a,c): {is_between(d,a,c)}")
                print(f"  between(f,a,b): {is_between(f,a,b)}")
                print(f"  ss(e,a,K): {same_side(e,a,d,f)}")
                print(f"  ss(e,d,M): {same_side(e,d,a,f)}")

    print(f"\n{'='*60}")
    print(f"AXIOM TEST 4 (with both between constraints):")
    print(f"  between(d,a,c) ∧ between(f,a,b)")
    print(f"  ∧ on(d,K) ∧ on(f,K) ∧ ¬on(a,K)")
    print(f"  ∧ ¬ss(e,a,K) ∧ ¬on(e,K)")
    print(f"  ∧ on(a,M) ∧ on(f,M) ∧ ¬on(d,M) ∧ ¬on(e,M)")
    print(f"  → ¬ss(e,d,M)")
    print(f"  Valid tests: {valid_tests}")
    print(f"  Violations:  {violations}")
    print(f"  Result:      {'PASS ✓' if violations == 0 else 'FAIL ✗'}")

    return violations == 0


if __name__ == "__main__":
    print("Testing proposed axioms with random coordinate geometry...")
    print("Each test uses 500,000 random configurations.\n")

    r1 = test_axiom()
    r2 = test_simpler_axiom()
    r3 = test_even_simpler()
    r4 = test_axiom_with_between_and_f()

    print(f"\n{'='*60}")
    print(f"SUMMARY:")
    print(f"  Test 1 (full):       {'PASS ✓' if r1 else 'FAIL ✗'}")
    print(f"  Test 2 (no between): {'PASS ✓' if r2 else 'FAIL ✗'}")
    print(f"  Test 3 (minimal):    {'PASS ✓' if r3 else 'FAIL ✗'}")
    print(f"  Test 4 (both betw):  {'PASS ✓' if r4 else 'FAIL ✗'}")
