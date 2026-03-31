"""
Test axiom validity with equidistance constraint (de=fe).

In I.9, e is the intersection of circles β(center d, through f) and 
γ(center f, through d). So de = df and fe = fd, meaning de = fe.
This makes e equidistant from d and f (on the perpendicular bisector of df).

Test if adding this constraint makes the interiority axiom valid.
"""
import math
import random
import sys

random.seed(42)

def cross2d(u, v):
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
    if n < 1e-12:
        return (1.0, 0.0)
    return (v[0]/n, v[1]/n)

def randn2():
    return (random.gauss(0,1), random.gauss(0,1))

def side_of_line(point, lp1, lp2):
    d = vsub(lp2, lp1)
    v = vsub(point, lp1)
    c = cross2d(d, v)
    if abs(c) < 1e-10:
        return 0
    return 1 if c > 0 else -1

def same_side(p, q, lp1, lp2):
    sp = side_of_line(p, lp1, lp2)
    sq = side_of_line(q, lp1, lp2)
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

def dist(a, b):
    return vnorm(vsub(b, a))

def intersect_circles(c1, r1, c2, r2):
    """Return both intersection points of two circles, or None."""
    d = dist(c1, c2)
    if d < 1e-12 or d > r1 + r2 + 1e-10 or d < abs(r1 - r2) - 1e-10:
        return None
    a = (r1*r1 - r2*r2 + d*d) / (2*d)
    h2 = r1*r1 - a*a
    if h2 < -1e-10:
        return None
    h = math.sqrt(max(0, h2))
    dx = (c2[0] - c1[0]) / d
    dy = (c2[1] - c1[1]) / d
    mx = c1[0] + a * dx
    my = c1[1] + a * dy
    p1 = (mx + h * dy, my - h * dx)
    p2 = (mx - h * dy, my + h * dx)
    return p1, p2

def test_with_equidistance(n_tests=500000):
    """
    Test: If e is equidistant from d and f (de=fe),
    and ¬ss(e,a,K) ∧ ¬on(e,K) ∧ ¬on(e,M) ∧ ¬on(d,M)
    ∧ on(d,K) ∧ on(f,K) ∧ on(a,M) ∧ on(f,M) ∧ ¬on(a,K)
    → ¬ss(e,d,M)

    This models I.9 where e = intersection of circles β(d,f) and γ(f,d),
    so de = df = fe = fd, making de = fe.
    """
    violations = 0
    valid_tests = 0

    for _ in range(n_tests):
        # Generate d, f as two distinct random points (forming line K)
        d = vscale(3, randn2())
        f = vscale(3, randn2())
        if dist(d, f) < 0.5:
            continue

        # K = line(d,f)
        # Generate a NOT on K
        a = vscale(3, randn2())
        if on_line(a, d, f):
            continue

        # M = line(a,f)
        # Check d not on M
        if on_line(d, a, f):
            continue

        # e is equidistant from d and f: de = fe
        # This means e is on the perpendicular bisector of df.
        # Generate e on that bisector.
        mid = vscale(0.5, vadd(d, f))
        df_dir = vnormalize(vsub(f, d))
        perp = (-df_dir[1], df_dir[0])
        t_e = random.gauss(0, 3)
        if abs(t_e) < 0.1:
            t_e = 0.5 * (1 if t_e >= 0 else -1)
        e = vadd(mid, vscale(t_e, perp))

        # Verify equidistance
        assert abs(dist(e, d) - dist(e, f)) < 1e-8, "e should be equidistant from d and f"

        # Check not-on conditions
        if on_line(e, d, f):  # on K
            continue
        if on_line(e, a, f):  # on M
            continue

        # Check ¬ss(e,a,K)
        ss_ea_K = same_side(e, a, d, f)
        if ss_ea_K is None or ss_ea_K:
            continue

        valid_tests += 1

        # Check conclusion: should be ¬ss(e,d,M)
        ss_ed_M = same_side(e, d, a, f)
        if ss_ed_M is None:
            continue

        if ss_ed_M:
            violations += 1
            if violations <= 5:
                print(f"\nVIOLATION #{violations}:")
                print(f"  d={d}, f={f}, a={a}, e={e}")
                print(f"  de={dist(e,d):.4f}, fe={dist(e,f):.4f}")
                print(f"  ¬on(a,K): {not on_line(a,d,f)}")
                print(f"  ¬on(d,M): {not on_line(d,a,f)}")
                print(f"  ¬on(e,K): {not on_line(e,d,f)}")
                print(f"  ¬on(e,M): {not on_line(e,a,f)}")
                print(f"  ss(e,a,K): {same_side(e,a,d,f)}")
                print(f"  ss(e,d,M): {same_side(e,d,a,f)} <- should be False!")

    print(f"\n{'='*60}")
    print(f"TEST WITH EQUIDISTANCE (de=fe):")
    print(f"  on(d,K) ∧ on(f,K) ∧ on(a,M) ∧ on(f,M)")
    print(f"  ∧ ¬on(a,K) ∧ ¬on(d,M) ∧ ¬on(e,K) ∧ ¬on(e,M)")
    print(f"  ∧ ¬ss(e,a,K) ∧ de=fe")
    print(f"  → ¬ss(e,d,M)")
    print(f"  Valid tests: {valid_tests}")
    print(f"  Violations:  {violations}")
    print(f"  Result:      {'PASS' if violations == 0 else 'FAIL'}")
    return violations == 0


def test_with_full_construction(n_tests=500000):
    """
    Test using the FULL I.9 construction:
    - between(d,a,c), between(f,a,b) 
    - d,a,c on line N; f,a,b on line M
    - K = line(d,f)
    - e = intersection of circles β(d, dist(d,f)) and γ(f, dist(f,d)) 
      on opposite side of K from a

    Conclusion: ¬ss(e,d,M) and ¬ss(e,f,N)
    """
    violations_M = 0
    violations_N = 0
    valid_tests = 0

    for _ in range(n_tests):
        # Generate point a
        a = vscale(2, randn2())

        # Generate line N through a: d-a-c
        n_dir = vnormalize(randn2())
        t_d = random.uniform(0.5, 3.0)
        t_c = random.uniform(0.5, 3.0)
        d = vsub(a, vscale(t_d, n_dir))  # d on opposite side from c
        c = vadd(a, vscale(t_c, n_dir))

        # Generate line M through a: f-a-b (NOT same as N)
        m_dir = randn2()
        mn = vnorm(m_dir)
        if mn < 0.01:
            continue
        m_dir = (m_dir[0]/mn, m_dir[1]/mn)
        if abs(cross2d(n_dir, m_dir)) < 0.1:
            continue

        t_f = random.uniform(0.5, 3.0)
        t_b = random.uniform(0.5, 3.0)
        f = vsub(a, vscale(t_f, m_dir))
        b = vadd(a, vscale(t_b, m_dir))

        # K = line(d,f)
        if dist(d, f) < 0.3:
            continue
        if on_line(a, d, f):
            continue

        # Circles: β centered at d through f, γ centered at f through d
        # Both have radius dist(d,f)
        r = dist(d, f)
        pts = intersect_circles(d, r, f, r)
        if pts is None:
            continue

        e1, e2 = pts
        if dist(e1, e2) < 1e-8:
            continue

        # Pick e on opposite side of K from a
        ss_e1a_K = same_side(e1, a, d, f)
        ss_e2a_K = same_side(e2, a, d, f)

        e = None
        if ss_e1a_K == False:
            e = e1
        elif ss_e2a_K == False:
            e = e2
        else:
            continue

        # Verify basic conditions
        if on_line(e, d, f):  # on K
            continue
        if on_line(e, a, f):  # on M
            continue
        if on_line(e, a, d):  # on N
            continue
        if on_line(d, a, f):  # d on M
            continue
        if on_line(f, a, d):  # f on N
            continue

        valid_tests += 1

        # Check ¬ss(e,d,M): e and d should be on opposite sides of M
        ss_ed_M = same_side(e, d, a, f)
        if ss_ed_M is True:
            violations_M += 1
            if violations_M <= 3:
                print(f"\nVIOLATION (ss(e,d,M)):")
                print(f"  a={a}, b={b}, c={c}, d={d}, f={f}, e={e}")
                print(f"  de={dist(e,d):.4f}, fe={dist(e,f):.4f}, df={dist(d,f):.4f}")
                print(f"  ss(e,a,K): {same_side(e,a,d,f)}")
                print(f"  ss(e,d,M): {same_side(e,d,a,f)} <- should be False!")

        # Check ¬ss(e,f,N): e and f should be on opposite sides of N
        ss_ef_N = same_side(e, f, a, d)
        if ss_ef_N is True:
            violations_N += 1
            if violations_N <= 3:
                print(f"\nVIOLATION (ss(e,f,N)):")
                print(f"  a={a}, b={b}, c={c}, d={d}, f={f}, e={e}")
                print(f"  ss(e,a,K): {same_side(e,a,d,f)}")
                print(f"  ss(e,f,N): {same_side(e,f,a,d)} <- should be False!")

    print(f"\n{'='*60}")
    print(f"TEST WITH FULL I.9 CONSTRUCTION:")
    print(f"  between(d,a,c), between(f,a,b)")
    print(f"  K=line(d,f), e = circles intersection opposite a wrt K")
    print(f"  de=df=fe=fd (equilateral triangle on df)")
    print(f"  Valid tests: {valid_tests}")
    print(f"  Violations ¬ss(e,d,M): {violations_M}")
    print(f"  Violations ¬ss(e,f,N): {violations_N}")
    print(f"  Result (M): {'PASS' if violations_M == 0 else 'FAIL'}")
    print(f"  Result (N): {'PASS' if violations_N == 0 else 'FAIL'}")
    return violations_M == 0 and violations_N == 0


def test_equidist_with_between(n_tests=500000):
    """
    Test with between(d,a,c) + equidistance de=fe.
    This is closer to what we have in the proof.
    """
    violations = 0
    valid_tests = 0

    for _ in range(n_tests):
        a = vscale(2, randn2())

        # N direction for between(d,a,c)
        n_dir = vnormalize(randn2())
        t_d = random.uniform(0.5, 3.0)
        d = vsub(a, vscale(t_d, n_dir))
        c = vadd(a, vscale(random.uniform(0.5, 3.0), n_dir))

        # f NOT on line N (d,a,c)
        f = vscale(3, randn2())
        if on_line(f, d, c):
            continue
        if dist(d, f) < 0.3:
            continue

        # M = line(a,f)
        if on_line(d, a, f):
            continue

        # K = line(d,f)
        if on_line(a, d, f):
            continue

        # e equidistant from d and f, on perp bisector of df
        mid = vscale(0.5, vadd(d, f))
        df_dir = vnormalize(vsub(f, d))
        perp = (-df_dir[1], df_dir[0])
        t_e = random.gauss(0, 3)
        if abs(t_e) < 0.1:
            t_e = 0.5 * (1 if t_e >= 0 else -1)
        e = vadd(mid, vscale(t_e, perp))

        if on_line(e, d, f) or on_line(e, a, f):
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
                print(f"  a={a}, d={d}, f={f}, e={e}")
                print(f"  between(d,a,c): {is_between(d,a,c)}")
                print(f"  de={dist(e,d):.4f}, fe={dist(e,f):.4f}")

    print(f"\n{'='*60}")
    print(f"TEST WITH between(d,a,c) + EQUIDISTANCE (de=fe):")
    print(f"  between(d,a,c) ∧ on(d,K) ∧ on(f,K) ∧ on(a,M) ∧ on(f,M)")
    print(f"  ∧ ¬on(a,K) ∧ ¬on(d,M) ∧ ¬on(e,K) ∧ ¬on(e,M)")
    print(f"  ∧ ¬ss(e,a,K) ∧ de=fe")
    print(f"  → ¬ss(e,d,M)")
    print(f"  Valid tests: {valid_tests}")
    print(f"  Violations:  {violations}")
    print(f"  Result:      {'PASS' if violations == 0 else 'FAIL'}")
    return violations == 0


if __name__ == "__main__":
    print("Testing axiom candidates with geometric verification...")
    print("Each test runs 500,000 random configurations.\n")

    r1 = test_with_equidistance()
    r2 = test_with_full_construction()
    r3 = test_equidist_with_between()

    print(f"\n{'='*60}")
    print("SUMMARY:")
    print(f"  Equidistance only:        {'PASS' if r1 else 'FAIL'}")
    print(f"  Full I.9 construction:    {'PASS' if r2 else 'FAIL'}")
    print(f"  between + equidistance:   {'PASS' if r3 else 'FAIL'}")
