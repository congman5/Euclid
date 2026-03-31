"""
Test the EXACT axiom formulation for I.9 using all available facts.
"""
import math
import random

random.seed(42)

def cross2d(u, v): return u[0]*v[1] - u[1]*v[0]
def vadd(a, b): return (a[0]+b[0], a[1]+b[1])
def vsub(a, b): return (a[0]-b[0], a[1]-b[1])
def vscale(s, v): return (s*v[0], s*v[1])
def vnorm(v): return math.sqrt(v[0]**2 + v[1]**2)
def vnormalize(v):
    n = vnorm(v)
    if n < 1e-12: return (1.0, 0.0)
    return (v[0]/n, v[1]/n)
def dist(a, b): return vnorm(vsub(b, a))
def randn2(): return (random.gauss(0,1), random.gauss(0,1))

def side_of_line(point, lp1, lp2):
    d = vsub(lp2, lp1)
    v = vsub(point, lp1)
    c = cross2d(d, v)
    if abs(c) < 1e-10: return 0
    return 1 if c > 0 else -1

def same_side(p, q, lp1, lp2):
    sp = side_of_line(p, lp1, lp2)
    sq = side_of_line(q, lp1, lp2)
    if sp == 0 or sq == 0: return None
    return sp == sq

def on_line(p, l1, l2):
    d = vsub(l2, l1)
    v = vsub(p, l1)
    return abs(cross2d(d, v)) < 1e-8

def is_between(d, a, c):
    dc = vsub(c, d)
    if vnorm(dc) < 1e-12: return False
    da = vsub(a, d)
    if abs(cross2d(dc, da)) > 1e-8: return False
    from math import sqrt
    t = (da[0]*dc[0]+da[1]*dc[1]) / (dc[0]*dc[0]+dc[1]*dc[1])
    return 0 < t < 1

def intersect_circles(c1, r1, c2, r2):
    d = dist(c1, c2)
    if d < 1e-12 or d > r1 + r2 + 1e-10 or d < abs(r1 - r2) - 1e-10:
        return None
    a = (r1*r1 - r2*r2 + d*d) / (2*d)
    h2 = r1*r1 - a*a
    if h2 < -1e-10: return None
    h = math.sqrt(max(0, h2))
    dx = (c2[0] - c1[0]) / d
    dy = (c2[1] - c1[1]) / d
    mx = c1[0] + a * dx
    my = c1[1] + a * dy
    return (mx + h*dy, my - h*dx), (mx - h*dy, my + h*dx)


def test_extend_opposite_full(n_tests=1000000):
    """
    EXTEND construction + OPPOSITE side, with ALL I.9 premises.

    Axiom P5 (proposed):
    between(d,a,c) ∧ between(f,a,b) ∧ on(d,K) ∧ on(f,K) 
    ∧ on(a,M) ∧ on(f,M) ∧ on(a,N) ∧ on(d,N)
    ∧ ¬on(c,M) ∧ ¬on(b,N)
    ∧ ¬ss(e,a,K) ∧ ¬on(e,K) ∧ ¬on(e,M) ∧ ¬on(e,N)
    → ss(e,c,M)

    With full I.9 construction: ad=af, circles, equilateral triangle.
    """
    violations_M = 0
    violations_N = 0
    valid = 0

    for _ in range(n_tests):
        a = vscale(2, randn2())

        n_dir = vnormalize(randn2())
        m_dir = randn2()
        mn = vnorm(m_dir)
        if mn < 0.01: continue
        m_dir = (m_dir[0]/mn, m_dir[1]/mn)
        if abs(cross2d(n_dir, m_dir)) < 0.05: continue

        r = random.uniform(0.5, 3.0)  # ad = af = r

        # Extension: d on opposite side of a from c on N
        d = vsub(a, vscale(r, n_dir))  # between(d,a,c)
        c = vadd(a, vscale(random.uniform(0.5, 3.0), n_dir))

        # Extension: f on opposite side of a from b on M  
        f = vsub(a, vscale(r, m_dir))  # between(f,a,b)
        b = vadd(a, vscale(random.uniform(0.5, 3.0), m_dir))

        if dist(d, f) < 0.3: continue
        if on_line(a, d, f): continue
        if on_line(d, a, f): continue
        if on_line(f, a, d): continue
        if on_line(c, a, f): continue  # c should not be on M
        if on_line(b, a, d): continue  # b should not be on N

        # Circles β(d,df) and γ(f,fd) for equilateral triangle
        df = dist(d, f)
        pts = intersect_circles(d, df, f, df)
        if pts is None: continue

        e1, e2 = pts
        if dist(e1, e2) < 1e-8: continue

        # e opposite a wrt K=line(d,f)
        ss1 = same_side(e1, a, d, f)
        ss2 = same_side(e2, a, d, f)
        e = None
        if ss1 is False: e = e1
        elif ss2 is False: e = e2
        else: continue

        if on_line(e, d, f): continue  # on K
        if on_line(e, a, f): continue  # on M
        if on_line(e, a, d): continue  # on N

        # Verify all premises
        assert is_between(d, a, c)
        assert is_between(f, a, b)
        assert not on_line(c, a, f)  # ¬on(c,M)
        assert not on_line(b, a, d)  # ¬on(b,N)

        valid += 1

        # Check ss(e,c,M): e and c on same side of M=line(a,f)
        ss_ec_M = same_side(e, c, a, f)
        if ss_ec_M is not True:
            violations_M += 1
            if violations_M <= 3:
                print(f"VIOLATION ss(e,c,M): a={a}, d={d}, f={f}, c={c}, b={b}, e={e}")
                print(f"  ss(e,c,M)={ss_ec_M}")

        # Check ss(e,b,N): e and b on same side of N=line(a,d)
        ss_eb_N = same_side(e, b, a, d)
        if ss_eb_N is not True:
            violations_N += 1
            if violations_N <= 3:
                print(f"VIOLATION ss(e,b,N): a={a}, d={d}, f={f}, c={c}, b={b}, e={e}")
                print(f"  ss(e,b,N)={ss_eb_N}")

    print(f"\n{'='*60}")
    print(f"EXTEND + OPPOSITE (full I.9 construction):")
    print(f"  Valid tests:            {valid}")
    print(f"  Violations ss(e,c,M):   {violations_M}")
    print(f"  Violations ss(e,b,N):   {violations_N}")
    print(f"  Result: {'PASS' if violations_M == 0 and violations_N == 0 else 'FAIL'}")
    return violations_M == 0 and violations_N == 0


def test_general_axiom(n_tests=1000000):
    """
    Test a GENERAL axiom (not requiring equilateral triangle):

    between(d,a,c) ∧ between(f,a,b) 
    ∧ on(a,M) ∧ on(f,M) ∧ on(a,N) ∧ on(d,N)
    ∧ on(d,K) ∧ on(f,K) 
    ∧ ¬on(c,M) ∧ ¬on(b,N) ∧ ¬on(a,K)
    ∧ ¬on(e,K) ∧ ¬on(e,M) ∧ ¬on(e,N) 
    ∧ ¬ss(e,a,K)
    → ss(e,c,M)

    No equilateral triangle constraint — just the diagrammatic facts.
    """
    violations = 0
    valid = 0

    for _ in range(n_tests):
        a = vscale(2, randn2())

        n_dir = vnormalize(randn2())
        m_dir = randn2()
        mn = vnorm(m_dir)
        if mn < 0.01: continue
        m_dir = (m_dir[0]/mn, m_dir[1]/mn)
        if abs(cross2d(n_dir, m_dir)) < 0.05: continue

        # d on extension of N past a
        td = random.uniform(0.5, 5.0)
        d = vsub(a, vscale(td, n_dir))
        c = vadd(a, vscale(random.uniform(0.5, 5.0), n_dir))

        # f on extension of M past a
        tf = random.uniform(0.5, 5.0)
        f = vsub(a, vscale(tf, m_dir))
        b = vadd(a, vscale(random.uniform(0.5, 5.0), m_dir))

        if dist(d, f) < 0.3: continue
        if on_line(a, d, f): continue
        if on_line(d, a, f): continue
        if on_line(f, a, d): continue
        if on_line(c, a, f): continue
        if on_line(b, a, d): continue

        # Random e NOT on K, M, N
        e = vscale(5, randn2())
        if on_line(e, d, f): continue  # on K
        if on_line(e, a, f): continue  # on M
        if on_line(e, a, d): continue  # on N

        # ¬ss(e,a,K)
        ss_ea = same_side(e, a, d, f)
        if ss_ea is None or ss_ea: continue

        valid += 1

        ss_ec_M = same_side(e, c, a, f)
        if ss_ec_M is not True:
            violations += 1
            if violations <= 3:
                print(f"VIOLATION: ss(e,c,M)={ss_ec_M}")
                print(f"  a={a}, d={d}, f={f}, c={c}, b={b}, e={e}")

    print(f"\n{'='*60}")
    print(f"GENERAL AXIOM (no equilateral triangle, random e):")
    print(f"  Valid tests:   {valid}")
    print(f"  Violations:    {violations}")
    print(f"  Result: {'PASS' if violations == 0 else 'FAIL'}")
    return violations == 0


if __name__ == "__main__":
    r1 = test_extend_opposite_full()
    r2 = test_general_axiom()
    print(f"\n{'='*60}")
    print(f"Full I.9 construction: {'PASS' if r1 else 'FAIL'}")
    print(f"General axiom:         {'PASS' if r2 else 'FAIL'}")
