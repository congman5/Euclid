"""
Test whether ¬ss(e,f,N) and ¬ss(e,d,M) are always true in the I.9 construction.
If YES: we can use TI2 to derive ss(e,c,M) and ss(e,b,N).
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


def test_missing_ss_facts():
    """
    Test ¬ss(e,f,N) and ¬ss(e,d,M) in the full I.9 construction.

    If these are ALWAYS true, then TI2 gives us ss(e,c,M) and ss(e,b,N).
    """
    n_tests = 2000000
    ss_ef_N_true = 0
    ss_ef_N_false = 0
    ss_ef_N_none = 0
    ss_ed_M_true = 0
    ss_ed_M_false = 0
    ss_ed_M_none = 0
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

        # ad = af = r (both on circle α)
        r = random.uniform(0.5, 4)
        d_pt = vadd(a, vscale(-r, dir_N))  # between(d,a,c)
        f = vadd(a, vscale(-r, dir_M))     # between(f,a,b)

        df = dist(d_pt, f)
        if df < 0.2:
            continue
        if on_line(a, d_pt, f):
            continue

        # Circles β(d,df) and γ(f,fd)
        pts = intersect_circles(d_pt, df, f, df)
        if pts is None:
            continue

        e1, e2 = pts
        if dist(e1, e2) < 1e-8:
            continue

        ss_e1a = same_side(e1, a, d_pt, f)
        ss_e2a = same_side(e2, a, d_pt, f)

        e = None
        if ss_e1a is False: e = e1
        elif ss_e2a is False: e = e2
        else: continue

        M1 = vadd(a, dir_M)
        N1 = vadd(a, dir_N)
        if on_line(e, a, M1) or on_line(e, a, N1):
            continue

        valid += 1

        # Test ss(e,f,N) — is e on same side of N as f?
        ss_ef_N = same_side(e, f, a, N1)
        if ss_ef_N is True: ss_ef_N_true += 1
        elif ss_ef_N is False: ss_ef_N_false += 1
        else: ss_ef_N_none += 1

        # Test ss(e,d,M) — is e on same side of M as d?
        ss_ed_M = same_side(e, d_pt, a, M1)
        if ss_ed_M is True: ss_ed_M_true += 1
        elif ss_ed_M is False: ss_ed_M_false += 1
        else: ss_ed_M_none += 1

    print(f"=== Missing SS facts for TI2 application ===")
    print(f"  Valid configurations: {valid}")
    print()
    print(f"  ss(e,f,N):  TRUE={ss_ef_N_true}  FALSE={ss_ef_N_false}  ON_LINE={ss_ef_N_none}")
    print(f"    Want ¬ss(e,f,N) = FALSE always: {ss_ef_N_true == 0}")
    print()
    print(f"  ss(e,d,M):  TRUE={ss_ed_M_true}  FALSE={ss_ed_M_false}  ON_LINE={ss_ed_M_none}")
    print(f"    Want ¬ss(e,d,M) = FALSE always: {ss_ed_M_true == 0}")


def test_ss_without_circles():
    """
    Same test but with e on perp bisector of df (de=fe), any distance.
    No circle constraint.
    """
    n_tests = 2000000
    ss_ef_N_true = 0
    ss_ef_N_false = 0
    ss_ed_M_true = 0
    ss_ed_M_false = 0
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

        ss_ef_N = same_side(e, f, a, N1)
        if ss_ef_N is True: ss_ef_N_true += 1
        else: ss_ef_N_false += 1

        ss_ed_M = same_side(e, d_pt, a, M1)
        if ss_ed_M is True: ss_ed_M_true += 1
        else: ss_ed_M_false += 1

    print()
    print(f"=== Without circles (just de=fe + opp side K) ===")
    print(f"  Valid: {valid}")
    print(f"  ss(e,f,N):  TRUE={ss_ef_N_true}  FALSE={ss_ef_N_false}")
    print(f"    ¬ss always? {ss_ef_N_true == 0}")
    print(f"  ss(e,d,M):  TRUE={ss_ed_M_true}  FALSE={ss_ed_M_false}")
    print(f"    ¬ss always? {ss_ed_M_true == 0}")


if __name__ == "__main__":
    test_missing_ss_facts()
    test_ss_without_circles()
