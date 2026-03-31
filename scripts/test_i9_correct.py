"""
Test Euclid's actual construction for I.9:
- D on segment AB (between A and B on arm M)
- F on segment AC (between A and C on arm N)  
- AD = AF (I.3)
- Equilateral triangle DFE constructed on DF (I.1)
- E on SAME side of line DF as A
"""
import math
import random

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

def dist(a, b):
    return vnorm(vsub(b, a))

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

def on_line(p, l1, l2):
    d = vsub(l2, l1)
    v = vsub(p, l1)
    return abs(cross2d(d, v)) < 1e-8

def intersect_circles(c1, r1, c2, r2):
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


def randn2():
    return (random.gauss(0,1), random.gauss(0,1))


def test_correct_construction(n_tests=500000):
    """
    Correct Euclid I.9 construction:
    - D between A and B on arm M (AD < AB, or just AD = some distance)
    - F between A and C on arm N (AF = AD)
    - E = intersection of circles(D,DF) and circles(F,FD) on same side of DF as A
    """
    counts = {
        'ss_ec_M': 0, 'nss_ec_M': 0,
        'ss_eb_N': 0, 'nss_eb_N': 0,
    }
    valid = 0

    for _ in range(n_tests):
        a = vscale(2, randn2())

        # Line M direction (arm AB)
        m_dir = vnormalize(randn2())
        # Line N direction (arm AC) - different from M
        n_dir = randn2()
        nn = vnorm(n_dir)
        if nn < 0.01:
            continue
        n_dir = (n_dir[0]/nn, n_dir[1]/nn)
        if abs(cross2d(m_dir, n_dir)) < 0.1:
            continue

        # b and c at various distances
        tb = random.uniform(1.0, 5.0)
        tc = random.uniform(1.0, 5.0)
        b = vadd(a, vscale(tb, m_dir))
        c = vadd(a, vscale(tc, n_dir))

        # D on segment AB: between(a, d, b)
        # F on segment AC: between(a, f, c), with AF = AD
        r = random.uniform(0.3, min(tb, tc) - 0.1)  # AD = AF = r < min(AB, AC)
        d_pt = vadd(a, vscale(r, m_dir))   # D on arm M
        f_pt = vadd(a, vscale(r, n_dir))   # F on arm N

        # Verify between
        # between(a, d, b) should be true
        # between(a, f, c) should be true

        if dist(d_pt, f_pt) < 0.2:
            continue
        if on_line(a, d_pt, f_pt):
            continue

        # K = line(D, F)
        # Circles: β = circle(D, DF), γ = circle(F, FD)
        df_dist = dist(d_pt, f_pt)
        pts = intersect_circles(d_pt, df_dist, f_pt, df_dist)
        if pts is None:
            continue

        e1, e2 = pts
        if dist(e1, e2) < 1e-8:
            continue

        # Pick E on SAME side of K(=line DF) as A
        ss_e1a = same_side(e1, a, d_pt, f_pt)
        ss_e2a = same_side(e2, a, d_pt, f_pt)

        e = None
        if ss_e1a is True:
            e = e1
        elif ss_e2a is True:
            e = e2
        else:
            continue

        if on_line(e, a, f_pt) or on_line(e, a, d_pt) or on_line(e, d_pt, f_pt):
            continue

        # Check d, f not on wrong lines
        if on_line(d_pt, a, f_pt):  # d on N
            continue
        if on_line(f_pt, a, d_pt):  # f on M
            continue

        valid += 1

        # M = line(a, b) = line(a, d)
        # N = line(a, c) = line(a, f)
        ss_ec = same_side(e, c, a, d_pt)  # same side of M (line through a,d which is arm AB)
        ss_eb = same_side(e, b, a, f_pt)  # same side of N (line through a,f which is arm AC)

        if ss_ec is True: counts['ss_ec_M'] += 1
        elif ss_ec is False: counts['nss_ec_M'] += 1

        if ss_eb is True: counts['ss_eb_N'] += 1
        elif ss_eb is False: counts['nss_eb_N'] += 1

    print(f"CORRECT Euclid construction (d between a,b; f between a,c):")
    print(f"  Valid tests: {valid}")
    print(f"  ss(e,c,M):  {counts['ss_ec_M']:6d} TRUE,  {counts['nss_ec_M']:6d} FALSE")
    print(f"  ss(e,b,N):  {counts['ss_eb_N']:6d} TRUE,  {counts['nss_eb_N']:6d} FALSE")
    t = counts['ss_ec_M'] + counts['nss_ec_M']
    if t > 0:
        print(f"  ss(e,c,M) TRUE: {100*counts['ss_ec_M']/t:.1f}%")
    t = counts['ss_eb_N'] + counts['nss_eb_N']
    if t > 0:
        print(f"  ss(e,b,N) TRUE: {100*counts['ss_eb_N']/t:.1f}%")


def test_extend_same_side(n_tests=500000):
    """
    Current proof construction but with e on SAME side:
    - d = extend from a past b on M (between(d,a,b))  -- WRONG, extend gives between(d,a,c) etc

    Actually current proof: d on extension of N past a (between(d,a,c)),
    f on extension of M past a (between(f,a,b)).

    What if we use same-side for e? e on same side of K as a.
    """
    counts = {
        'ss_ec_M': 0, 'nss_ec_M': 0,
        'ss_eb_N': 0, 'nss_eb_N': 0,
    }
    valid = 0

    for _ in range(n_tests):
        a = vscale(2, randn2())

        n_dir = vnormalize(randn2())
        m_dir = randn2()
        mn = vnorm(m_dir)
        if mn < 0.01:
            continue
        m_dir = (m_dir[0]/mn, m_dir[1]/mn)
        if abs(cross2d(n_dir, m_dir)) < 0.1:
            continue

        r = random.uniform(1.0, 3.0)

        # Extensions: d opposite c from a on N, f opposite b from a on M
        d = vsub(a, vscale(r, n_dir))   # between(d,a,c)
        c = vadd(a, vscale(random.uniform(0.5, 3.0), n_dir))

        f = vsub(a, vscale(r, m_dir))   # between(f,a,b)
        b = vadd(a, vscale(random.uniform(0.5, 3.0), m_dir))

        if dist(d, f) < 0.3:
            continue
        if on_line(a, d, f):
            continue

        df_dist = dist(d, f)
        pts = intersect_circles(d, df_dist, f, df_dist)
        if pts is None:
            continue

        e1, e2 = pts
        if dist(e1, e2) < 1e-8:
            continue

        # Pick e on SAME side of K as a
        ss_e1a = same_side(e1, a, d, f)
        ss_e2a = same_side(e2, a, d, f)

        e = None
        if ss_e1a is True:
            e = e1
        elif ss_e2a is True:
            e = e2
        else:
            continue

        if on_line(e, a, f) or on_line(e, a, d) or on_line(e, d, f):
            continue
        if on_line(d, a, f) or on_line(f, a, d):
            continue

        valid += 1

        # M = line(a,f) = line(a,b), N = line(a,d) = line(a,c)
        ss_ec = same_side(e, c, a, f)  # M
        ss_eb = same_side(e, b, a, d)  # N

        if ss_ec is True: counts['ss_ec_M'] += 1
        elif ss_ec is False: counts['nss_ec_M'] += 1

        if ss_eb is True: counts['ss_eb_N'] += 1
        elif ss_eb is False: counts['nss_eb_N'] += 1

    print(f"\nExtend construction + e SAME side as a:")
    print(f"  Valid tests: {valid}")
    print(f"  ss(e,c,M):  {counts['ss_ec_M']:6d} TRUE,  {counts['nss_ec_M']:6d} FALSE")
    print(f"  ss(e,b,N):  {counts['ss_eb_N']:6d} TRUE,  {counts['nss_eb_N']:6d} FALSE")
    t = counts['ss_ec_M'] + counts['nss_ec_M']
    if t > 0:
        print(f"  ss(e,c,M) TRUE: {100*counts['ss_ec_M']/t:.1f}%")
    t = counts['ss_eb_N'] + counts['nss_eb_N']
    if t > 0:
        print(f"  ss(e,b,N) TRUE: {100*counts['ss_eb_N']/t:.1f}%")


if __name__ == "__main__":
    test_correct_construction()
    test_extend_same_side()
