"""
Directly test what same-side relationships hold in the I.9 construction.
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


def full_i9_test(n_tests=500000):
    """
    Full I.9 construction: 
    - between(d,a,c) on N, between(f,a,b) on M
    - ad = af (equal radii)
    - K = line(d,f)
    - β = circle(d, dist(d,f)), γ = circle(f, dist(f,d))
    - e = intersection on opposite side of K from a

    Check: ss(e,c,M)? ss(e,b,N)? ss(e,d,M)? ss(e,f,N)?
    """
    counts = {
        'ss_ec_M': 0, 'nss_ec_M': 0,
        'ss_eb_N': 0, 'nss_eb_N': 0,
        'ss_ed_M': 0, 'nss_ed_M': 0,
        'ss_ef_N': 0, 'nss_ef_N': 0,
    }
    valid = 0

    for _ in range(n_tests):
        a = vscale(2, randn2())

        # Line N: d-a-c
        n_dir = vnormalize(randn2())
        r = random.uniform(1.0, 3.0)  # ad = af = r (circle α radius)
        d = vsub(a, vscale(r, n_dir))
        c = vadd(a, vscale(random.uniform(0.5, 3.0), n_dir))

        # Line M: f-a-b  
        m_dir = randn2()
        mn = vnorm(m_dir)
        if mn < 0.01:
            continue
        m_dir = (m_dir[0]/mn, m_dir[1]/mn)
        if abs(cross2d(n_dir, m_dir)) < 0.1:
            continue

        f = vsub(a, vscale(r, m_dir))  # af = r = ad
        b = vadd(a, vscale(random.uniform(0.5, 3.0), m_dir))

        # Verify
        assert abs(dist(a, d) - dist(a, f)) < 1e-8

        if dist(d, f) < 0.3:
            continue
        if on_line(a, d, f):
            continue
        if on_line(d, a, f):
            continue
        if on_line(f, a, d):
            continue

        # Circles β(d, df) and γ(f, fd)
        df = dist(d, f)
        pts = intersect_circles(d, df, f, df)
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

        if on_line(e, d, f) or on_line(e, a, f) or on_line(e, a, d):
            continue

        valid += 1

        # Check all same-side relationships
        ss_ec_M = same_side(e, c, a, f)
        ss_eb_N = same_side(e, b, a, d)
        ss_ed_M = same_side(e, d, a, f)
        ss_ef_N = same_side(e, f, a, d)

        if ss_ec_M is True: counts['ss_ec_M'] += 1
        elif ss_ec_M is False: counts['nss_ec_M'] += 1

        if ss_eb_N is True: counts['ss_eb_N'] += 1
        elif ss_eb_N is False: counts['nss_eb_N'] += 1

        if ss_ed_M is True: counts['ss_ed_M'] += 1
        elif ss_ed_M is False: counts['nss_ed_M'] += 1

        if ss_ef_N is True: counts['ss_ef_N'] += 1
        elif ss_ef_N is False: counts['nss_ef_N'] += 1

    print(f"Full I.9 construction — {valid} valid tests:")
    print(f"  ss(e,c,M):  {counts['ss_ec_M']:6d} TRUE,  {counts['nss_ec_M']:6d} FALSE")
    print(f"  ss(e,b,N):  {counts['ss_eb_N']:6d} TRUE,  {counts['nss_eb_N']:6d} FALSE")
    print(f"  ss(e,d,M):  {counts['ss_ed_M']:6d} TRUE,  {counts['nss_ed_M']:6d} FALSE")
    print(f"  ss(e,f,N):  {counts['ss_ef_N']:6d} TRUE,  {counts['nss_ef_N']:6d} FALSE")

    total_ec = counts['ss_ec_M'] + counts['nss_ec_M']
    total_eb = counts['ss_eb_N'] + counts['nss_eb_N']
    if total_ec > 0:
        print(f"\n  ss(e,c,M) is TRUE {100*counts['ss_ec_M']/total_ec:.1f}% of the time")
    if total_eb > 0:
        print(f"  ss(e,b,N) is TRUE {100*counts['ss_eb_N']/total_eb:.1f}% of the time")

def randn2():
    return (random.gauss(0,1), random.gauss(0,1))

if __name__ == "__main__":
    full_i9_test()
