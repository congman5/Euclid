"""
Test whether a new construction rule + opposite side gives correct ss results.

New rule: given that we have one intersection d1 of line N with circle α
(via extend, so between(d1,a,c)), construct d2 = the OTHER intersection,
which satisfies between(d1,a,d2) = between(a,d2,...). 

Actually simpler: just construct d on arm N (between a and c) at distance r=ab from a.
Then f on arm M (between a and b) at same distance.
K = line(d,f). e = opposite side of K from a, on circles β(d,df) and γ(f,fd).

This is the paper's exact construction. We already proved it gives 100% TRUE.
The question is: can we ADD a construction rule to System E that allows this?
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


def test_arm_construction_with_ss():
    """
    Full I.9 with points on ARMS + opposite:
    - d on arm N: between(a,d,c) — but we need ad < ac for this
    - f on arm M: between(a,f,b) — need af < ab for this
    - ad = af = r (some radius, must be < min(ab,ac))
    - K = line(d,f)
    - e opposite K from a, on circles β(d,df)∩γ(f,fd)

    Test: ss(e,c,M) and ss(e,b,N)
    Also test: what facts does the construction produce?
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

        tb = random.uniform(2, 5)
        b = vadd(a, vscale(tb, dir_M))
        tc = random.uniform(2, 5)
        c = vadd(a, vscale(tc, dir_N))

        # r must be less than both ab and ac so points are ON arms
        r = random.uniform(0.5, min(tb, tc) - 0.1)

        # d on arm N: between(a,d,c), distance r from a
        d_pt = vadd(a, vscale(r, dir_N))
        # f on arm M: between(a,f,b), distance r from a
        f = vadd(a, vscale(r, dir_M))

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
        ss_ec_M = same_side(e, c, a, M1)
        ss_eb_N = same_side(e, b, a, N1)
        if ss_ec_M is not True:
            violations_M += 1
        if ss_eb_N is not True:
            violations_N += 1

    print(f"=== ARM construction (d,f on arms) + opposite side ===")
    print(f"  Valid: {valid}")
    print(f"  ss(e,c,M) violations: {violations_M}")
    print(f"  ss(e,b,N) violations: {violations_N}")
    print(f"  BOTH ALWAYS TRUE: {violations_M == 0 and violations_N == 0}")
    print()


def test_new_construction_conclusions():
    """
    If we add a new construction rule:

    let-intersection-line-circle-same-side-as:
      Prerequisites: on(d1,α), on(d1,L), inside(a,α), on(a,L), on(c,L), a≠c, d1≠a
                     ¬same-side(d1,c,a) -- WAIT this doesn't work, same-side is about lines

    Actually, let's think about it differently:

    let-intersection-line-circle-other:
      Prerequisites: on(d1,α), on(d1,L), inside(a,α), on(a,L), between(d1,a,c_ref)
                     [d1 is the extend-side intersection, c_ref is any point on L beyond a from d1]
      Conclusion: on(d2,α), on(d2,L), between(a,d2,d1_mapped_to_c_ref_side)

    Hmm this is getting complex. Let me think about what MINIMAL new rule would work.

    The simplest: given the extend construction produced d1 with between(d1,a,c),
    produce d2 on the OTHER side:

    Prerequisites: on(d1,α), on(d1,L), inside(a,α), on(a,L), between(d1,a,c), on(c,L)
    Conclusion: on(d2,α), on(d2,L), between(d1,a,d2), between(a,d2,c)

    Wait — between(a,d2,c) requires d2 between a and c. But if c is inside α,
    d2 could be beyond c. Hmm.

    Actually: from C1, between(d1,a,d2) always holds. And between(a,d2,c) vs 
    between(a,c,d2) depends on whether c is closer or farther than d2.

    For I.9: if ad < ac (r < distance to c), then d2 is between a and c: between(a,d2,c). ✓
    But for general c, we can't guarantee this.

    What if the conclusion is just: on(d2,α), on(d2,L), between(d1,a,d2)?
    Then d2 is on the opposite side of a from d1 on L. This is always true.

    Combined with c being on N beyond d2: between(a,d2,c) follows from 
    ad2 = ad1 (both on circle) and ... hmm no, we'd need to know the ordering.

    Let's test what conclusions are always true.
    """
    print("Test: what new construction conclusions are always true?")
    print()

    n_tests = 2000000
    btw_d1_a_d2 = 0  # between(d1,a,d2)
    btw_a_d2_c = 0   # between(a,d2,c) — d2 on arm
    btw_a_c_d2 = 0   # between(a,c,d2) — d2 beyond c
    d2_eq_c = 0      # d2 = c (degenerate)
    valid = 0

    for _ in range(n_tests):
        a = (random.uniform(-3, 3), random.uniform(-3, 3))

        theta_N = random.uniform(0, 2*math.pi)
        dir_N = (math.cos(theta_N), math.sin(theta_N))

        # c on N
        tc = random.uniform(0.5, 5)
        c = vadd(a, vscale(tc, dir_N))

        # Circle α centered at a with random radius
        r = random.uniform(0.3, 6)

        # d1 = extend side intersection (between(d1,a,c))
        d1 = vadd(a, vscale(-r, dir_N))

        # d2 = arm side intersection  
        d2 = vadd(a, vscale(r, dir_N))

        valid += 1

        # Check betweenness
        # between(d1,a,d2): always true since d1 and d2 are on opposite sides
        btw_d1_a_d2 += 1

        # Is d2 between a and c? Only if r < tc
        if abs(r - tc) < 1e-8:
            d2_eq_c += 1
        elif r < tc:
            btw_a_d2_c += 1  # d2 on arm between a and c
        else:
            btw_a_c_d2 += 1  # d2 beyond c

    print(f"  Valid: {valid}")
    print(f"  between(d1,a,d2): {btw_d1_a_d2} (always {btw_d1_a_d2 == valid})")
    print(f"  between(a,d2,c): {btw_a_d2_c} ({100*btw_a_d2_c/valid:.1f}%) — d2 on arm")
    print(f"  between(a,c,d2): {btw_a_c_d2} ({100*btw_a_c_d2/valid:.1f}%) — d2 beyond c")
    print(f"  d2 = c: {d2_eq_c} ({100*d2_eq_c/valid:.1f}%) — degenerate")
    print()
    print("  ==> between(d1,a,d2) is ALWAYS true (the only guaranteed conclusion)")
    print("  ==> between(a,d2,c) depends on r vs tc — NOT always true")


if __name__ == "__main__":
    test_arm_construction_with_ss()
    test_new_construction_conclusions()
