"""
Test axiom with equidistance constraint: de = fe means e is on 
perpendicular bisector of segment df, on opposite side of K from a.
"""
import math
import random

random.seed(42)

def cross2d(u, v): return u[0]*v[1] - u[1]*v[0]
def vadd(a, b): return (a[0]+b[0], a[1]+b[1])
def vsub(a, b): return (a[0]-b[0], a[1]-b[1])
def vscale(s, v): return (s*v[0], s*v[1])
def vnorm(v): return math.sqrt(v[0]**2 + v[1]**2)
def dist(a, b): return vnorm(vsub(b, a))

def side_of_line(point, lp1, lp2):
    d = vsub(lp2, lp1)
    v = vsub(point, lp1)
    c = cross2d(d, v)
    if abs(c) < 1e-9: return 0
    return 1 if c > 0 else -1

def same_side(p, q, lp1, lp2):
    sp = side_of_line(p, lp1, lp2)
    sq = side_of_line(q, lp1, lp2)
    if sp == 0 or sq == 0: return None
    return sp == sq

def on_line(p, l1, l2):
    return side_of_line(p, l1, l2) == 0

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


def test_with_equidistance():
    """
    Test with de=fe (e equidistant from d and f) + on opposite side of K from a.

    This is the EXACT I.9 situation:
    - M, N through a (angle arms)
    - b on M, c on N  
    - d on N extended past a: between(d,a,c)
    - f on M extended past a: between(f,a,b)
    - K = line(d,f)
    - e: de = fe, ¬ss(e,a,K), ¬on(e,K)
    - ad = af (both on circle α)

    Then: ss(e,c,M) and ss(e,b,N)?
    """
    n_tests = 2000000
    violations_M = 0
    violations_N = 0
    valid = 0

    for _ in range(n_tests):
        a = (random.uniform(-3, 3), random.uniform(-3, 3))

        theta_M = random.uniform(0, 2*math.pi)
        dir_M = (math.cos(theta_M), math.sin(theta_M))
        theta_N = random.uniform(0, 2*math.pi)
        dir_N = (math.cos(theta_N), math.sin(theta_N))

        if abs(cross2d(dir_M, dir_N)) < 0.1:
            continue

        # b on M, c on N
        tb = random.uniform(1, 5)
        b = vadd(a, vscale(tb, dir_M))
        tc = random.uniform(1, 5)
        c = vadd(a, vscale(tc, dir_N))

        # d = extension past a from c on N, at distance r from a
        # f = extension past a from b on M, at distance r from a
        r = random.uniform(0.5, 4)
        d_pt = vadd(a, vscale(-r, dir_N))  # between(d,a,c)
        f = vadd(a, vscale(-r, dir_M))     # between(f,a,b), ad=af=r

        df = dist(d_pt, f)
        if df < 0.2:
            continue

        K_d, K_f = d_pt, f
        if on_line(a, K_d, K_f):
            continue

        # Circles β(d, df) and γ(f, fd)
        pts = intersect_circles(d_pt, df, f, df)
        if pts is None:
            continue

        e1, e2 = pts
        if dist(e1, e2) < 1e-8:
            continue

        # e = intersection on opposite side of K from a
        ss_e1a = same_side(e1, a, K_d, K_f)
        ss_e2a = same_side(e2, a, K_d, K_f)

        e = None
        if ss_e1a is False: e = e1
        elif ss_e2a is False: e = e2
        else: continue

        M1 = vadd(a, dir_M)
        N1 = vadd(a, dir_N)
        if on_line(e, a, M1) or on_line(e, a, N1):
            continue

        valid += 1
        ss_ec_M = same_side(e, c, a, M1)
        ss_eb_N = same_side(e, b, a, N1)
        if ss_ec_M is not True:
            violations_M += 1
        if ss_eb_N is not True:
            violations_N += 1

    print(f"=== Full I.9 construction (extend+opposite+circles) ===")
    print(f"  ad=af, circles β(d,df) γ(f,df), e=opp side of K from a")
    print(f"  Valid: {valid}")
    print(f"  ss(e,c,M) violations: {violations_M}")
    print(f"  ss(e,b,N) violations: {violations_N}")
    print(f"  BOTH ALWAYS TRUE: {violations_M == 0 and violations_N == 0}")
    print()


def test_with_perp_bisector_only():
    """
    Test with just de=fe (perpendicular bisector of df) but 
    e at ANY distance, not just df distance. Plus opposite side from a.

    The key insight: e being on the perp bisector of df AND on opp side 
    of K from a might be sufficient WITHOUT the full circle constraint.
    """
    n_tests = 2000000
    violations_M = 0
    violations_N = 0
    valid = 0

    for _ in range(n_tests):
        a = (random.uniform(-3, 3), random.uniform(-3, 3))

        theta_M = random.uniform(0, 2*math.pi)
        dir_M = (math.cos(theta_M), math.sin(theta_M))
        theta_N = random.uniform(0, 2*math.pi)
        dir_N = (math.cos(theta_N), math.sin(theta_N))

        if abs(cross2d(dir_M, dir_N)) < 0.1:
            continue

        tb = random.uniform(1, 5)
        b = vadd(a, vscale(tb, dir_M))
        tc = random.uniform(1, 5)
        c = vadd(a, vscale(tc, dir_N))

        r = random.uniform(0.5, 4)
        d_pt = vadd(a, vscale(-r, dir_N))
        f = vadd(a, vscale(-r, dir_M))

        df = dist(d_pt, f)
        if df < 0.2:
            continue

        if on_line(a, d_pt, f):
            continue

        # e on perpendicular bisector of df, opposite side of K from a
        # Perp bisector: midpoint of df + perpendicular direction
        mid = vscale(0.5, vadd(d_pt, f))
        df_dir = vsub(f, d_pt)
        perp = (-df_dir[1], df_dir[0])  # perpendicular to df

        # Choose t randomly
        t = random.uniform(-5, 5)
        e = vadd(mid, vscale(t, perp))

        ss_ea_K = same_side(e, a, d_pt, f)
        if ss_ea_K is not False:
            continue
        if on_line(e, d_pt, f):
            continue

        M1 = vadd(a, dir_M)
        N1 = vadd(a, dir_N)
        if on_line(e, a, M1) or on_line(e, a, N1):
            continue

        valid += 1
        ss_ec_M = same_side(e, c, a, M1)
        ss_eb_N = same_side(e, b, a, N1)
        if ss_ec_M is not True:
            violations_M += 1
        if ss_eb_N is not True:
            violations_N += 1

    print(f"=== Perp bisector + opposite side (de=fe, any distance) ===")
    print(f"  Valid: {valid}")
    print(f"  ss(e,c,M) violations: {violations_M}")
    print(f"  ss(e,b,N) violations: {violations_N}")
    print(f"  BOTH ALWAYS TRUE: {violations_M == 0 and violations_N == 0}")
    print()


def test_minimal_axiom():
    """
    Test the MOST MINIMAL axiom that could work:

    on(a,M), on(a,N), M≠N,
    on(b,M), ¬on(b,N),
    on(c,N), ¬on(c,M),
    on(d,N), between(d,a,c),  [d on extension past a from c]
    on(f,M), between(f,a,b),  [f on extension past a from b]
    K = line(d,f), ¬on(a,K),
    ¬on(e,M), ¬on(e,K),
    ¬ss(e,a,K),  [e opp side of K from a]
    de = fe      [e equidistant from d and f]
    => ss(e,c,M)

    This uses ONLY the structure we have. No circles needed in the axiom.
    The equidistance de=fe is the key metric condition.
    """
    n_tests = 2000000
    violations_M = 0
    violations_N = 0
    valid = 0

    for _ in range(n_tests):
        a = (random.uniform(-3, 3), random.uniform(-3, 3))

        theta_M = random.uniform(0, 2*math.pi)
        dir_M = (math.cos(theta_M), math.sin(theta_M))
        theta_N = random.uniform(0, 2*math.pi)
        dir_N = (math.cos(theta_N), math.sin(theta_N))

        if abs(cross2d(dir_M, dir_N)) < 0.1:
            continue

        tb = random.uniform(1, 5)
        b = vadd(a, vscale(tb, dir_M))
        tc = random.uniform(1, 5)
        c = vadd(a, vscale(tc, dir_N))

        # d on opposite side of a from c on N
        td = random.uniform(0.5, 5)
        d_pt = vadd(a, vscale(-td, dir_N))

        # f on opposite side of a from b on M
        tf = random.uniform(0.5, 5)
        f = vadd(a, vscale(-tf, dir_M))

        # NOTE: ad ≠ af in general here (not requiring this)

        df = dist(d_pt, f)
        if df < 0.2:
            continue

        if on_line(a, d_pt, f):
            continue

        # e on perp bisector of df (so de=fe), opposite side from a
        mid = vscale(0.5, vadd(d_pt, f))
        df_dir = vsub(f, d_pt)
        perp = (-df_dir[1], df_dir[0])

        t = random.uniform(-5, 5)
        e = vadd(mid, vscale(t, perp))

        ss_ea_K = same_side(e, a, d_pt, f)
        if ss_ea_K is not False:
            continue
        if on_line(e, d_pt, f):
            continue

        M1 = vadd(a, dir_M)
        N1 = vadd(a, dir_N)
        if on_line(e, a, M1) or on_line(e, a, N1):
            continue

        valid += 1
        ss_ec_M = same_side(e, c, a, M1)
        ss_eb_N = same_side(e, b, a, N1)
        if ss_ec_M is not True:
            violations_M += 1
        if ss_eb_N is not True:
            violations_N += 1

    print(f"=== Minimal axiom: de=fe + opp side K + between conditions ===")
    print(f"  (ad and af independent, not necessarily equal)")
    print(f"  Valid: {valid}")
    print(f"  ss(e,c,M) violations: {violations_M}")
    print(f"  ss(e,b,N) violations: {violations_N}")
    print(f"  BOTH ALWAYS TRUE: {violations_M == 0 and violations_N == 0}")
    print()


def test_minimal_with_ad_eq_af():
    """Same as minimal but with ad = af (as in I.9 construction)."""
    n_tests = 2000000
    violations_M = 0
    violations_N = 0
    valid = 0

    for _ in range(n_tests):
        a = (random.uniform(-3, 3), random.uniform(-3, 3))

        theta_M = random.uniform(0, 2*math.pi)
        dir_M = (math.cos(theta_M), math.sin(theta_M))
        theta_N = random.uniform(0, 2*math.pi)
        dir_N = (math.cos(theta_N), math.sin(theta_N))

        if abs(cross2d(dir_M, dir_N)) < 0.1:
            continue

        tb = random.uniform(1, 5)
        b = vadd(a, vscale(tb, dir_M))
        tc = random.uniform(1, 5)
        c = vadd(a, vscale(tc, dir_N))

        # ad = af = r
        r = random.uniform(0.5, 5)
        d_pt = vadd(a, vscale(-r, dir_N))
        f = vadd(a, vscale(-r, dir_M))

        df = dist(d_pt, f)
        if df < 0.2:
            continue

        if on_line(a, d_pt, f):
            continue

        # e on perp bisector of df, opposite side from a
        mid = vscale(0.5, vadd(d_pt, f))
        df_dir = vsub(f, d_pt)
        perp = (-df_dir[1], df_dir[0])

        t = random.uniform(-5, 5)
        e = vadd(mid, vscale(t, perp))

        ss_ea_K = same_side(e, a, d_pt, f)
        if ss_ea_K is not False:
            continue
        if on_line(e, d_pt, f):
            continue

        M1 = vadd(a, dir_M)
        N1 = vadd(a, dir_N)
        if on_line(e, a, M1) or on_line(e, a, N1):
            continue

        valid += 1
        ss_ec_M = same_side(e, c, a, M1)
        ss_eb_N = same_side(e, b, a, N1)
        if ss_ec_M is not True:
            violations_M += 1
        if ss_eb_N is not True:
            violations_N += 1

    print(f"=== Minimal + ad=af: de=fe + opp side K + ad=af ===")
    print(f"  Valid: {valid}")
    print(f"  ss(e,c,M) violations: {violations_M}")
    print(f"  ss(e,b,N) violations: {violations_N}")
    print(f"  BOTH ALWAYS TRUE: {violations_M == 0 and violations_N == 0}")


if __name__ == "__main__":
    test_with_equidistance()
    test_with_perp_bisector_only()
    test_minimal_axiom()
    test_minimal_with_ad_eq_af()
