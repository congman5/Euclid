"""
Test the EXACT axiom needed for I.9's same-side derivation.

We test this with the ACTUAL extend+opposite construction (the one used in the proof):
- between(d,a,c): d on extension of N past a from c
- between(f,a,b): f on extension of M past a from b  
- e on opposite side of K=line(d,f) from a
- e on circles β(d,df) and γ(f,fd) — equidistant from d and f

The question: under what EXACT conditions is ss(e,c,M) always true?

From the existing axioms we can derive:
- ss(a,c,K): from P2 + between(d,a,c) + on(d,K) + ¬on(a,K)
- ¬ss(e,a,K): construction gives this
- Therefore ¬ss(e,c,K): from SS4 contrapositive

So e and c are on OPPOSITE sides of K.

Now: can we connect "e and c on opposite sides of K" + 
"M passes through a and f, where f is ON K and a is NOT on K"
to "e and c on same side of M"?

Geometrically: K separates e from c. M crosses K at f. 
The question is whether e ends up on c's side of M.
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


def test_general_pasch_interior():
    """
    Test a general Pasch-interior axiom:

    If three lines L, M, N meet at a point 'a':
      on(a,L), on(a,M), on(a,N)
    with points b on L, c on M, d on N such that:
      on(b,L), on(c,M), on(d,N)
      ¬on(b,M), ¬on(b,N), ¬on(c,L), ¬on(c,N), ¬on(d,L), ¬on(d,M)
    and K = line(b,d) with:
      ¬on(a,K), ¬on(c,K)
    and:
      ss(a,c,K) — a and c on same side of K
      ¬ss(e,a,K) — e on opposite side of K from a  
      ¬on(e,K), ¬on(e,L), ¬on(e,M), ¬on(e,N)
    Then:
      ss(e,c,M)?

    This is the GENERAL form — no circles, no equidistance.
    Just the Pasch-interior principle.
    """
    n_tests = 1000000
    violations = 0
    valid = 0

    for _ in range(n_tests):
        # Random point a
        a = (random.uniform(-5, 5), random.uniform(-5, 5))

        # Three lines through a (directions)
        theta_L = random.uniform(0, math.pi)
        theta_M = random.uniform(0, math.pi)
        theta_N = random.uniform(0, math.pi)

        # Ensure lines are distinct (not too close)
        dirs = [theta_L, theta_M, theta_N]
        diffs = []
        for i in range(3):
            for j in range(i+1, 3):
                d = abs(dirs[i] - dirs[j])
                d = min(d, math.pi - d)
                diffs.append(d)
        if min(diffs) < 0.1:
            continue

        dir_L = (math.cos(theta_L), math.sin(theta_L))
        dir_M = (math.cos(theta_M), math.sin(theta_M))
        dir_N = (math.cos(theta_N), math.sin(theta_N))

        # b on L (away from a)
        tb = random.choice([-1, 1]) * random.uniform(1, 5)
        b = vadd(a, vscale(tb, dir_L))

        # c on M
        tc = random.choice([-1, 1]) * random.uniform(1, 5)
        c = vadd(a, vscale(tc, dir_M))

        # d on N
        td = random.choice([-1, 1]) * random.uniform(1, 5)
        d_pt = vadd(a, vscale(td, dir_N))

        # K = line(b, d)
        if dist(b, d_pt) < 0.1:
            continue

        # Check: ¬on(a,K), ¬on(c,K)
        if on_line(a, b, d_pt):
            continue
        if on_line(c, b, d_pt):
            continue

        # Check: ss(a,c,K)
        ss_ac_K = same_side(a, c, b, d_pt)
        if ss_ac_K is not True:
            continue

        # e is a random point on opposite side of K from a
        # and not on L, M, N, K
        for _attempt in range(5):
            e = (random.uniform(-10, 10), random.uniform(-10, 10))
            ss_ea_K = same_side(e, a, b, d_pt)
            if ss_ea_K is not False:
                continue
            if on_line(e, b, d_pt):
                continue
            # Check ¬on(e,L), ¬on(e,M), ¬on(e,N)
            L1 = vadd(a, dir_L)
            M1 = vadd(a, dir_M)
            N1 = vadd(a, dir_N)
            if on_line(e, a, L1) or on_line(e, a, M1) or on_line(e, a, N1):
                continue

            valid += 1

            # Test: ss(e,c,M)?
            ss_ec_M = same_side(e, c, a, M1)
            if ss_ec_M is not True:
                violations += 1
            break

    print(f"General Pasch-interior test (3 lines + opp side K):")
    print(f"  Valid: {valid}, Violations: {violations}")
    print(f"  ALWAYS TRUE: {violations == 0}")
    print()


def test_pasch_interior_with_both_between():
    """
    Test with the FULL I.9 conditions on b,d positions relative to arms:

    between(d,a,c) means a is between d and c on N  
    between(f,a,b) means a is between f and b on M
    K = line(d,f)
    e on opposite side of K from a
    ¬on(e,M), ¬on(e,N)

    Then: ss(e,c,M)?

    NOTE: d and f are on EXTENSIONS past a, not on arms.
    But we derived ss(a,c,K) from P2.
    """
    n_tests = 1000000
    violations = 0
    valid = 0

    for _ in range(n_tests):
        a = (random.uniform(-3, 3), random.uniform(-3, 3))

        # M direction (for b and f)
        theta_M = random.uniform(0, 2*math.pi)
        dir_M = (math.cos(theta_M), math.sin(theta_M))

        # N direction (for c and d) — must be different from M
        theta_N = random.uniform(0, 2*math.pi)
        dir_N = (math.cos(theta_N), math.sin(theta_N))

        if abs(cross2d(dir_M, dir_N)) < 0.1:
            continue

        # b on M, same side as dir_M
        tb = random.uniform(1, 5)
        b = vadd(a, vscale(tb, dir_M))

        # f on M, OPPOSITE side from b (between(f,a,b) means a between f and b)
        tf = random.uniform(0.5, 5)
        f = vadd(a, vscale(-tf, dir_M))  # opposite direction from b

        # c on N, same side as dir_N
        tc = random.uniform(1, 5)
        c = vadd(a, vscale(tc, dir_N))

        # d on N, OPPOSITE side from c (between(d,a,c) means a between d and c)
        td = random.uniform(0.5, 5)
        d_pt = vadd(a, vscale(-td, dir_N))  # opposite direction from c

        # K = line(d,f)
        if dist(d_pt, f) < 0.1:
            continue

        # Check ¬on(a,K)
        if on_line(a, d_pt, f):
            continue

        # Verify ss(a,c,K) — should always be true from P2
        ss_ac_K = same_side(a, c, d_pt, f)
        if ss_ac_K is not True:
            continue

        # e on opposite side of K from a, not on M or N or K
        for _attempt in range(10):
            e = (random.uniform(-10, 10), random.uniform(-10, 10))
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
            if ss_ec_M is not True:
                violations += 1
            break

    print(f"Pasch-interior with between(d,a,c) + between(f,a,b):")
    print(f"  Valid: {valid}, Violations: {violations}")
    print(f"  ALWAYS TRUE: {violations == 0}")
    print()


def test_pasch_interior_symmetric():
    """
    Test BOTH conclusions needed for I.9:
    ss(e,c,M) AND ss(e,b,N)

    With between(d,a,c), between(f,a,b), ¬ss(e,a,K), ¬on(e,K),
    ¬on(e,M), ¬on(e,N), ss(a,c,K), ss(a,b,K)
    """
    n_tests = 1000000
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
        tf = random.uniform(0.5, 5)
        f = vadd(a, vscale(-tf, dir_M))
        tc = random.uniform(1, 5)
        c = vadd(a, vscale(tc, dir_N))
        td = random.uniform(0.5, 5)
        d_pt = vadd(a, vscale(-td, dir_N))

        if dist(d_pt, f) < 0.1:
            continue
        if on_line(a, d_pt, f):
            continue

        ss_ac_K = same_side(a, c, d_pt, f)
        ss_ab_K = same_side(a, b, d_pt, f)
        if ss_ac_K is not True or ss_ab_K is not True:
            continue

        for _attempt in range(10):
            e = (random.uniform(-10, 10), random.uniform(-10, 10))
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
            break

    print(f"Symmetric test (both ss goals, no circles):")
    print(f"  Valid: {valid}")
    print(f"  ss(e,c,M) violations: {violations_M}")
    print(f"  ss(e,b,N) violations: {violations_N}")
    print(f"  BOTH ALWAYS TRUE: {violations_M == 0 and violations_N == 0}")
    print()


def test_ti_like_axiom():
    """
    Test a TI-like axiom that's NOT in the paper:

    Three lines L, M, N meeting at a.
    b on L (and only L), c on M (and only M), d on N (and only N).
    ss(c,d,L) — c and d on same side of L
    ¬ss(e,a,K) where K=line(c,d) — e on opposite side of K from a
    ¬on(e,K), ¬on(e,L), ¬on(e,M), ¬on(e,N)
    => ss(e,d,M) ∧ ss(e,c,N)

    In our I.9 context:
    L=K=line(d,f), M and N are the angle arms.
    Wait, this doesn't map well.

    Let me try a more direct formulation.
    """
    pass


def test_pasch4_variant():
    """
    Test an axiom based on Pasch's axiom extended to opposite-side:

    Pasch 4 says: L≠M, on(b,L), on(b,M), on(a,M), on(c,M), 
                  a≠b, c≠b, ¬ss(a,c,L) → between(a,b,c)

    What about: on(a,M), on(f,M), on(f,K), on(d,K),
                between(f,a,b) [so f,a,b on M in that order],
                ¬on(e,M), ¬on(e,K),
                ¬ss(e,a,K)
                → ss(e,c,M) ?

    This is too specific. Let me try the actual general principle.
    """
    pass


def test_interior_crossbar():
    """
    Test the CROSSBAR theorem / interior axiom:

    If a ray from vertex a passes through the interior of angle bac
    (meaning it goes between the two arms), then points on the 
    opposite side of this ray from a are inside the angle.

    More precisely:
    on(a,M), on(b,M), on(a,N), on(c,N), ¬on(c,M), ¬on(b,N)
    on(d,K), on(f,K) where d is on N-side, f is on M-side
    ¬on(a,K)
    ss(a,c,K) [a and c on same side of K — verified true from P2]
    ss(a,b,K) [a and b on same side of K — verified true from P2]
    ¬ss(e,a,K) [e on opposite side from a]
    ¬on(e,M), ¬on(e,N), ¬on(e,K)
    => ss(e,c,M) ∧ ss(e,b,N)

    This is the INTERIOR principle: K "crosses through" the angle
    (since d is connected to N-side and f to M-side), and e being
    on the opposite side of K from the vertex a means e is INSIDE
    the angle (same side as c relative to M, same side as b relative to N).
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

        # b on M, c on N (on the "positive" arm direction)
        tb = random.uniform(1, 5)
        b = vadd(a, vscale(tb, dir_M))
        tc = random.uniform(1, 5)
        c = vadd(a, vscale(tc, dir_N))

        # d on N-ray (could be same or opposite side of a from c)
        # For I.9: between(d,a,c) means d is on opposite side of a from c
        td = random.uniform(0.5, 5)
        d_pt = vadd(a, vscale(-td, dir_N))  # opposite side from c

        # f on M-ray (could be same or opposite side of a from b)
        # For I.9: between(f,a,b) means f is on opposite side of a from b
        tf = random.uniform(0.5, 5)
        f = vadd(a, vscale(-tf, dir_M))  # opposite side from b

        # K = line(d,f)
        if dist(d_pt, f) < 0.1:
            continue
        if on_line(a, d_pt, f):
            continue

        # CRITICAL CHECKS:
        # ss(a,c,K) and ss(a,b,K) must both be true
        # (These are derived from P2 in the proof)
        ss_ac_K = same_side(a, c, d_pt, f)
        ss_ab_K = same_side(a, b, d_pt, f)
        if ss_ac_K is not True or ss_ab_K is not True:
            continue

        # e on opposite side of K from a
        for _attempt in range(10):
            e = (random.uniform(-10, 10), random.uniform(-10, 10))
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
            break

    print(f"=== INTERIOR/CROSSBAR axiom test ===")
    print(f"  Conditions: 3 lines at a, d on opp(c) on N, f on opp(b) on M,")
    print(f"              K=line(d,f), ss(a,c,K), ss(a,b,K), ¬ss(e,a,K)")
    print(f"  Valid: {valid}")
    print(f"  ss(e,c,M) violations: {violations_M}")
    print(f"  ss(e,b,N) violations: {violations_N}")
    print(f"  BOTH ALWAYS TRUE: {violations_M == 0 and violations_N == 0}")


if __name__ == "__main__":
    test_interior_crossbar()
    test_pasch_interior_symmetric()
