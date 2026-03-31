"""
Test paper's exact I.9 description:
- d on arm M (between a and b), e on arm N (between a and c), ad=ae
- K_de = line(d,e)
- Equilateral triangle: circles β(d,de) and γ(e,ed)
- f = intersection opposite a relative to K_de
"""
import math
import random

random.seed(42)

def cross2d(u, v): return u[0]*v[1] - u[1]*v[0]
def vadd(a, b): return (a[0]+b[0], a[1]+b[1])
def vsub(a, b): return (a[0]-b[0], a[1]-b[1])
def vscale(s, v): return (s*v[0], s*v[1])
def vnorm(v): return math.sqrt(v[0]**2 + v[1]**2)
def vdot(a, b): return a[0]*b[0] + a[1]*b[1]
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

def angle_between_dirs(d1, d2):
    dot = d1[0]*d2[0] + d1[1]*d2[1]
    return math.degrees(math.acos(max(-1, min(1, dot))))

def test_paper_construction(n_tests=500000):
    """Paper's construction: d,e on arms, f opposite a wrt line(d,e)."""
    bins = [(0,30),(30,60),(60,90),(90,120),(120,150),(150,180)]
    res_fc_M = {b: [0,0] for b in bins}  # [true, false] for ss(f,c,M)
    res_fb_N = {b: [0,0] for b in bins}  # [true, false] for ss(f,b,N)
    valid = 0

    for _ in range(n_tests):
        a = vscale(2, randn2())
        m_dir = vnormalize(randn2())
        n_dir = randn2()
        nn = vnorm(n_dir)
        if nn < 0.01: continue
        n_dir = (n_dir[0]/nn, n_dir[1]/nn)
        if abs(cross2d(m_dir, n_dir)) < 0.05: continue

        angle = angle_between_dirs(m_dir, n_dir)

        tb = random.uniform(2.0, 5.0)
        tc = random.uniform(2.0, 5.0)
        b = vadd(a, vscale(tb, m_dir))
        c = vadd(a, vscale(tc, n_dir))

        # d on arm AB, e_pt on arm AC, ad = ae
        r = random.uniform(0.5, min(tb, tc) - 0.1)
        d_pt = vadd(a, vscale(r, m_dir))   # d on arm M (AB)
        e_pt = vadd(a, vscale(r, n_dir))   # e on arm N (AC)

        de = dist(d_pt, e_pt)
        if de < 0.2: continue
        if on_line(a, d_pt, e_pt): continue

        # Equilateral triangle on de: circles β(d,de) γ(e,de)
        pts = intersect_circles(d_pt, de, e_pt, de)
        if pts is None: continue

        f1, f2 = pts
        if dist(f1, f2) < 1e-8: continue

        # f = opposite a wrt line(d,e)
        ss_f1a = same_side(f1, a, d_pt, e_pt)
        ss_f2a = same_side(f2, a, d_pt, e_pt)

        f = None
        if ss_f1a is False: f = f1
        elif ss_f2a is False: f = f2
        else: continue

        if on_line(f, a, d_pt) or on_line(f, a, e_pt) or on_line(f, d_pt, e_pt):
            continue

        valid += 1

        # Check ss(f,c,M) where M=line(a,b)=line(a,d)
        ss_fc = same_side(f, c, a, d_pt)
        # Check ss(f,b,N) where N=line(a,c)=line(a,e)
        ss_fb = same_side(f, b, a, e_pt)

        for (lo,hi) in bins:
            if lo <= angle < hi:
                if ss_fc is True: res_fc_M[(lo,hi)][0] += 1
                elif ss_fc is False: res_fc_M[(lo,hi)][1] += 1
                if ss_fb is True: res_fb_N[(lo,hi)][0] += 1
                elif ss_fb is False: res_fb_N[(lo,hi)][1] += 1
                break

    print(f"Paper construction (d,e on arms, f opposite a) — {valid} valid:")
    print(f"{'Angle':>10s}  {'ss(f,c,M) T':>12s}  {'F':>8s}  {'%T':>6s}  {'ss(f,b,N) T':>12s}  {'F':>8s}  {'%T':>6s}")
    for (lo,hi) in bins:
        t1,f1 = res_fc_M[(lo,hi)]
        t2,f2 = res_fb_N[(lo,hi)]
        tot1 = t1+f1; tot2 = t2+f2
        p1 = 100*t1/tot1 if tot1 else 0
        p2 = 100*t2/tot2 if tot2 else 0
        print(f"  {lo:3d}-{hi:3d}°  {t1:12d}  {f1:8d}  {p1:5.1f}%  {t2:12d}  {f2:8d}  {p2:5.1f}%")


def test_paper_same_side(n_tests=500000):
    """Paper construction but f on SAME side as a."""
    bins = [(0,30),(30,60),(60,90),(90,120),(120,150),(150,180)]
    res_fc_M = {b: [0,0] for b in bins}
    valid = 0

    for _ in range(n_tests):
        a = vscale(2, randn2())
        m_dir = vnormalize(randn2())
        n_dir = randn2()
        nn = vnorm(n_dir)
        if nn < 0.01: continue
        n_dir = (n_dir[0]/nn, n_dir[1]/nn)
        if abs(cross2d(m_dir, n_dir)) < 0.05: continue

        angle = angle_between_dirs(m_dir, n_dir)

        tb = random.uniform(2.0, 5.0)
        tc = random.uniform(2.0, 5.0)
        b = vadd(a, vscale(tb, m_dir))
        c = vadd(a, vscale(tc, n_dir))

        r = random.uniform(0.5, min(tb, tc) - 0.1)
        d_pt = vadd(a, vscale(r, m_dir))
        e_pt = vadd(a, vscale(r, n_dir))

        de = dist(d_pt, e_pt)
        if de < 0.2: continue
        if on_line(a, d_pt, e_pt): continue

        pts = intersect_circles(d_pt, de, e_pt, de)
        if pts is None: continue

        f1, f2 = pts
        if dist(f1, f2) < 1e-8: continue

        # f = SAME side as a wrt line(d,e)
        ss_f1a = same_side(f1, a, d_pt, e_pt)
        ss_f2a = same_side(f2, a, d_pt, e_pt)

        f = None
        if ss_f1a is True: f = f1
        elif ss_f2a is True: f = f2
        else: continue

        if on_line(f, a, d_pt) or on_line(f, a, e_pt) or on_line(f, d_pt, e_pt):
            continue

        valid += 1

        ss_fc = same_side(f, c, a, d_pt)

        for (lo,hi) in bins:
            if lo <= angle < hi:
                if ss_fc is True: res_fc_M[(lo,hi)][0] += 1
                elif ss_fc is False: res_fc_M[(lo,hi)][1] += 1
                break

    print(f"\nPaper construction but f SAME side as a — {valid} valid:")
    print(f"{'Angle':>10s}  {'ss(f,c,M) T':>12s}  {'F':>8s}  {'%T':>6s}")
    for (lo,hi) in bins:
        t,f_c = res_fc_M[(lo,hi)]
        tot = t+f_c
        p = 100*t/tot if tot else 0
        print(f"  {lo:3d}-{hi:3d}°  {t:12d}  {f_c:8d}  {p:5.1f}%")


if __name__ == "__main__":
    test_paper_construction()
    test_paper_same_side()
