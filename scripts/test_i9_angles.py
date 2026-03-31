"""
Test with restricted angle sizes.
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


def angle_between_dirs(d1, d2):
    """Angle in degrees between two unit vectors."""
    dot = d1[0]*d2[0] + d1[1]*d2[1]
    dot = max(-1, min(1, dot))
    return math.degrees(math.acos(dot))


def test_extend_same_side_by_angle(n_tests=500000):
    """
    Current proof construction (extend) + e on same side as a.
    Group results by angle size.
    """
    bins = [(0, 30), (30, 60), (60, 90), (90, 120), (120, 150), (150, 180)]
    results = {b: {'true': 0, 'false': 0} for b in bins}

    for _ in range(n_tests):
        a = vscale(2, randn2())

        n_dir = vnormalize(randn2())
        m_dir = randn2()
        mn = vnorm(m_dir)
        if mn < 0.01:
            continue
        m_dir = (m_dir[0]/mn, m_dir[1]/mn)
        if abs(cross2d(n_dir, m_dir)) < 0.05:
            continue

        # Angle between arms (b and c are in positive direction)
        angle = angle_between_dirs(m_dir, n_dir)

        r = random.uniform(1.0, 3.0)

        # Extensions
        d = vsub(a, vscale(r, n_dir))
        c = vadd(a, vscale(random.uniform(0.5, 3.0), n_dir))
        f = vsub(a, vscale(r, m_dir))
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

        ss_ec = same_side(e, c, a, f)
        if ss_ec is None:
            continue

        for (lo, hi) in bins:
            if lo <= angle < hi:
                if ss_ec:
                    results[(lo, hi)]['true'] += 1
                else:
                    results[(lo, hi)]['false'] += 1
                break

    print("Extend construction + e SAME side as a, by angle ∠bac:")
    print(f"{'Angle range':>15s}  {'TRUE':>8s}  {'FALSE':>8s}  {'% TRUE':>8s}")
    for (lo, hi) in bins:
        t = results[(lo, hi)]['true']
        f = results[(lo, hi)]['false']
        total = t + f
        pct = 100*t/total if total > 0 else 0
        print(f"  {lo:3d}° - {hi:3d}°   {t:8d}  {f:8d}  {pct:7.1f}%")


def test_correct_by_angle(n_tests=500000):
    """
    Correct construction (d between a,b; f between a,c) + e same side as a.
    """
    bins = [(0, 30), (30, 60), (60, 90), (90, 120), (120, 150), (150, 180)]
    results = {b: {'true': 0, 'false': 0} for b in bins}

    for _ in range(n_tests):
        a = vscale(2, randn2())

        m_dir = vnormalize(randn2())
        n_dir = randn2()
        nn = vnorm(n_dir)
        if nn < 0.01:
            continue
        n_dir = (n_dir[0]/nn, n_dir[1]/nn)
        if abs(cross2d(m_dir, n_dir)) < 0.05:
            continue

        angle = angle_between_dirs(m_dir, n_dir)

        tb = random.uniform(2.0, 5.0)
        tc = random.uniform(2.0, 5.0)
        b = vadd(a, vscale(tb, m_dir))
        c = vadd(a, vscale(tc, n_dir))

        r = random.uniform(0.5, min(tb, tc) - 0.1)
        d_pt = vadd(a, vscale(r, m_dir))   # D on arm AB
        f_pt = vadd(a, vscale(r, n_dir))   # F on arm AC

        if dist(d_pt, f_pt) < 0.2:
            continue
        if on_line(a, d_pt, f_pt):
            continue

        df_dist = dist(d_pt, f_pt)
        pts = intersect_circles(d_pt, df_dist, f_pt, df_dist)
        if pts is None:
            continue

        e1, e2 = pts
        if dist(e1, e2) < 1e-8:
            continue

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
        if on_line(d_pt, a, f_pt) or on_line(f_pt, a, d_pt):
            continue

        # M = line(a, d) = line(a, b)
        ss_ec = same_side(e, c, a, d_pt)  
        if ss_ec is None:
            continue

        for (lo, hi) in bins:
            if lo <= angle < hi:
                if ss_ec:
                    results[(lo, hi)]['true'] += 1
                else:
                    results[(lo, hi)]['false'] += 1
                break

    print("\nCorrect construction (d on arm AB, f on arm AC), e same side as a:")
    print(f"{'Angle range':>15s}  {'TRUE':>8s}  {'FALSE':>8s}  {'% TRUE':>8s}")
    for (lo, hi) in bins:
        t = results[(lo, hi)]['true']
        f = results[(lo, hi)]['false']
        total = t + f
        pct = 100*t/total if total > 0 else 0
        print(f"  {lo:3d}° - {hi:3d}°   {t:8d}  {f:8d}  {pct:7.1f}%")


if __name__ == "__main__":
    test_extend_same_side_by_angle()
    test_correct_by_angle()
