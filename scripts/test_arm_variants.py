"""
Test I.9 construction variant where f=b (since b is already on circle α and arm M).
Then d is on arm N at distance ab from a, K=line(d,b), e opposite side from a.
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


def test_db_construction():
    """
    f = b (on circle α and on arm M).
    d on arm N at distance ab from a (on circle α).
    K = line(d,b).
    e = circle β(d,db) ∩ γ(b,bd), opposite side of K from a.

    Test: 
    1. ∠bae = ∠cae (angle bisection)
    2. ss(e,c,M) 
    3. ss(e,b,N)
    """
    n_tests = 2000000
    angle_ok = 0
    angle_fail = 0
    ss_ec_M_true = 0
    ss_ec_M_false = 0
    ss_eb_N_true = 0
    ss_eb_N_false = 0
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

        # f = b (already on circle α centered at a through b)
        # d on arm N at distance ab from a
        r = tb  # radius of circle α = ab

        # d needs to be on arm N (between a and c): need r < tc
        if r >= tc - 0.1:
            continue

        d_pt = vadd(a, vscale(r, dir_N))  # between(a,d,c)

        # K = line(d, b)
        db = dist(d_pt, b)
        if db < 0.2:
            continue
        if on_line(a, d_pt, b):
            continue

        # Circles β(d, db) and γ(b, bd) 
        pts = intersect_circles(d_pt, db, b, db)
        if pts is None:
            continue

        e1, e2 = pts
        if dist(e1, e2) < 1e-8:
            continue

        ss_e1a = same_side(e1, a, d_pt, b)
        ss_e2a = same_side(e2, a, d_pt, b)

        e = None
        if ss_e1a is False: e = e1
        elif ss_e2a is False: e = e2
        else: continue

        M1 = vadd(a, dir_M)
        N1 = vadd(a, dir_N)
        if on_line(e, a, M1) or on_line(e, a, N1):
            continue

        valid += 1

        # Check angle bisection: ∠bae = ∠cae
        def angle(p, vertex, q):
            v1 = vsub(p, vertex)
            v2 = vsub(q, vertex)
            n1 = vnorm(v1)
            n2 = vnorm(v2)
            if n1 < 1e-10 or n2 < 1e-10:
                return 0
            cos = (v1[0]*v2[0] + v1[1]*v2[1]) / (n1 * n2)
            return math.acos(max(-1, min(1, cos)))

        ang_bae = angle(b, a, e)
        ang_cae = angle(c, a, e)
        if abs(ang_bae - ang_cae) < 1e-6:
            angle_ok += 1
        else:
            angle_fail += 1

        # Check ss
        ss_ec = same_side(e, c, a, M1)
        ss_eb = same_side(e, b, a, N1)
        if ss_ec is True: ss_ec_M_true += 1
        else: ss_ec_M_false += 1
        if ss_eb is True: ss_eb_N_true += 1
        else: ss_eb_N_false += 1

    print(f"=== d on arm N, f=b construction ===")
    print(f"  Valid: {valid}")
    print(f"  ∠bae = ∠cae: OK={angle_ok} FAIL={angle_fail}")
    print(f"  ss(e,c,M): TRUE={ss_ec_M_true}  FALSE={ss_ec_M_false}")
    print(f"  ss(e,b,N): TRUE={ss_eb_N_true}  FALSE={ss_eb_N_false}")
    print()


def test_symmetric_arm_construction():
    """
    d on arm N at distance r from a (between(a,d,c))
    f on arm M at distance r from a (between(a,f,b))
    r < min(tb, tc) so both are truly on arms.
    K = line(d,f)
    e = opposite side of K from a, on circles β(d,df) ∩ γ(f,fd)

    This is the paper's exact construction.
    """
    n_tests = 2000000
    angle_ok = 0
    angle_fail = 0
    ss_ec_M_true = 0
    ss_ec_M_false = 0
    ss_eb_N_true = 0
    ss_eb_N_false = 0
    valid = 0

    for _ in range(n_tests):
        a = (random.uniform(-3, 3), random.uniform(-3, 3))

        theta_M = random.uniform(0, 2*math.pi)
        dir_M = (math.cos(theta_M), math.sin(theta_M))
        theta_N = random.uniform(0, 2*math.pi)
        dir_N = (math.cos(theta_N), math.sin(theta_N))

        if abs(cross2d(dir_M, dir_N)) < 0.1:
            continue

        tb = random.uniform(2, 5)
        b = vadd(a, vscale(tb, dir_M))
        tc = random.uniform(2, 5)
        c = vadd(a, vscale(tc, dir_N))

        r = random.uniform(0.5, min(tb, tc) - 0.1)
        d_pt = vadd(a, vscale(r, dir_N))  # between(a,d,c)
        f = vadd(a, vscale(r, dir_M))     # between(a,f,b)

        df = dist(d_pt, f)
        if df < 0.2:
            continue
        if on_line(a, d_pt, f):
            continue

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

        def angle(p, vertex, q):
            v1 = vsub(p, vertex)
            v2 = vsub(q, vertex)
            n1 = vnorm(v1)
            n2 = vnorm(v2)
            if n1 < 1e-10 or n2 < 1e-10:
                return 0
            cos = (v1[0]*v2[0] + v1[1]*v2[1]) / (n1 * n2)
            return math.acos(max(-1, min(1, cos)))

        ang_bae = angle(b, a, e)
        ang_cae = angle(c, a, e)
        if abs(ang_bae - ang_cae) < 1e-6:
            angle_ok += 1
        else:
            angle_fail += 1

        ss_ec = same_side(e, c, a, M1)
        ss_eb = same_side(e, b, a, N1)
        if ss_ec is True: ss_ec_M_true += 1
        else: ss_ec_M_false += 1
        if ss_eb is True: ss_eb_N_true += 1
        else: ss_eb_N_false += 1

    print(f"=== Symmetric arm construction (d,f on arms, r < min(tb,tc)) ===")
    print(f"  Valid: {valid}")
    print(f"  ∠bae = ∠cae: OK={angle_ok} FAIL={angle_fail}")
    print(f"  ss(e,c,M): TRUE={ss_ec_M_true}  FALSE={ss_ec_M_false}")
    print(f"  ss(e,b,N): TRUE={ss_eb_N_true}  FALSE={ss_eb_N_false}")


if __name__ == "__main__":
    test_db_construction()
    test_symmetric_arm_construction()
