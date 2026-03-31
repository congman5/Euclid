"""Test: is the following TRUE?

Given the FULL I.9 construction facts available to rule 9:
- intersects(β,γ), center(d,β), center(b,γ), on(d,K), on(b,K), ¬on(a,K)
- e = opposite-side intersection: on(e,β), on(e,γ), ¬ss(e,a,K), ¬on(e,K)

ADDITIONALLY:
- on(a,M), on(b,M), ¬on(d,M), ¬on(e,M)  (line M through a,b)
- ss(d,c,M)  (d and c same side of M, already proved)

CONCLUDE: ss(e,c,M)

Actually simpler — test if ss(e,a,K) being false + standard Pasch facts 
give us ¬ss(g,e,M) where between(g,a,c) and on(a,M).

Let me just test: between(g,a,c) ∧ on(a,M) ∧ ¬on(g,M) ∧ ¬on(e,M) ∧ ¬ss(e,a,K) ∧ on(a,K)...

Actually, let me just directly test what additional info the opposite-side 
construction gives us with Pasch.

CLAIM: ¬on(a,K) ∧ ¬ss(e,a,K) ∧ on(b,K) ∧ on(a,M) ∧ on(b,M) ∧ K≠M ∧ ¬on(e,M)
       → ss(e,a,M)  (e is on same side of M as a — wait, a is ON M)

That doesn't work. a is on M so ss(e,a,M) isn't meaningful.

Let me think about what P2 gives us.
P2: between(a,b,c) ∧ on(a,L) ∧ ¬on(b,L) → ss(b,c,L)

In I.9: between(g,a,d) ∧ on(a,M) ∧ ¬on(g,M) → ss(g,d,...) wait, g and d
are the outer points, a is between them. So P2 with between(g,a,d), on(a,M), ¬on(g,M)
→ ss(g,d,M)? NO — P2 says between(a,b,c)∧on(a,L)→ss(b,c,L), so the first 
point of between is the one on the line. 

Wait: P2: between(a,b,c) ∧ on(a,L) ∧ ¬on(b,L) → ss(b,c,L)
With between(g,a,d), the "a" in the axiom pattern maps to g, "b" to a, "c" to d.
So: on(g,L) ∧ ¬on(a,L) → ss(a,d,L). But a IS on M, so this doesn't help.

Remap: with a-mapping=a (the vertex, which IS on M), b-mapping=g, c-mapping=d:
between(a,g,d)? We have between(g,a,d), not between(a,g,d).
B1a: between(a,b,c) → between(c,b,a). So between(g,a,d) → between(d,a,g).
Then between(d,a,g) with on(d,...) — but d is not on M.

Actually, P2 with between(d,a,g): map a→d, b→a, c→g.
on(d,L) ∧ ¬on(a,L) → ss(a,g,L). But we need L=K (d is on K).
So: on(d,K) ∧ ¬on(a,K) → ss(a,g,K).
That gives us ss(a,g,K)! And we have ¬ss(e,a,K) from construction.
By SS2: ss(a,g,K) → ss(g,a,K).

Now, ¬ss(e,a,K) and ss(g,a,K):
SS4: ss(g,a,K) ∧ ss(g,e,K) → ss(a,e,K). But we want the negative.

Let's think: ¬ss(e,a,K) means e and a are on opposite sides of K (or one is on K).
e is not on K. a is not on K. So they're on opposite sides.
ss(a,g,K) means a and g are on same side.
So g is on same side as a, opposite side from e.
Therefore ¬ss(g,e,K).

Formally: Suppose ss(g,e,K). Then by SS4: ss(g,a,K) ∧ ss(g,e,K) → ss(a,e,K).
But we have ¬ss(a,e,K) [= ¬ss(e,a,K) by SS2 contrapositive]. Contradiction.
So ¬ss(g,e,K).

Now I have ¬ss(g,e,K) AND ¬on(g,K) AND ¬on(e,K).
Apply SS5 with a=g, b=e, c=c, L=K:... but I need ¬on(c,K).
Hmm, c might not be relevant here.

Wait, what I really want is ¬ss(g,e,M). Let me see if I can get that.

g is on extension of N past a. 
e is on opposite side of K from a.

Hmm, g and e relative to M... this requires more Pasch reasoning.

Let me just check numerically: in the I.9 setup, is ¬ss(g,e,M) always true?
"""
import random, math

def cross2d(ox, oy, ax, ay, bx, by):
    return (ax - ox) * (by - oy) - (ay - oy) * (bx - ox)

def same_side(px, py, qx, qy, lx1, ly1, lx2, ly2):
    cp = cross2d(lx1, ly1, lx2, ly2, px, py)
    cq = cross2d(lx1, ly1, lx2, ly2, qx, qy)
    return cp * cq > 0

def on_line(px, py, lx1, ly1, lx2, ly2, tol=1e-9):
    return abs(cross2d(lx1, ly1, lx2, ly2, px, py)) < tol

def circle_circle_intersections(cx1, cy1, r1, cx2, cy2, r2):
    ddx, ddy = cx2 - cx1, cy2 - cy1
    d = math.hypot(ddx, ddy)
    if d < 1e-12 or d > r1 + r2 + 1e-12 or d < abs(r1 - r2) - 1e-12:
        return []
    a_val = (r1*r1 - r2*r2 + d*d) / (2*d)
    h2 = r1*r1 - a_val*a_val
    if h2 < -1e-12:
        return []
    h = math.sqrt(max(0, h2))
    mx, my = cx1 + a_val*ddx/d, cy1 + a_val*ddy/d
    px, py = -ddy/d, ddx/d
    return [(mx + h*px, my + h*py), (mx - h*px, my - h*py)]

random.seed(42)
tested = 0
violations_nss_ge_M = 0  # want ¬ss(g,e,M) to be TRUE, i.e., ss(g,e,M) = False
violations_nss_fe_N = 0  # want ¬ss(f,e,N) similarly

for _ in range(2_000_000):
    ax, ay = random.uniform(-5, 5), random.uniform(-5, 5)
    bx, by = random.uniform(-5, 5), random.uniform(-5, 5)
    if math.hypot(bx-ax, by-ay) < 0.3:
        continue
    cx, cy = random.uniform(-5, 5), random.uniform(-5, 5)
    if math.hypot(cx-ax, cy-ay) < 0.3:
        continue
    if on_line(cx, cy, ax, ay, bx, by, tol=0.01):
        continue
    if on_line(bx, by, ax, ay, cx, cy, tol=0.01):
        continue

    # d on ray a->c at distance ab from a
    dist_ab = math.hypot(bx-ax, by-ay)
    dist_ac = math.hypot(cx-ax, cy-ay)
    ddx = ax + dist_ab * (cx-ax)/dist_ac
    ddy = ay + dist_ab * (cy-ay)/dist_ac

    # g = extension of N past a: between(g,a,c)
    # g is on the opposite side of a from c on line N
    gx = ax - (cx-ax)/dist_ac * dist_ab  # arbitrary distance, use dist_ab
    gy = ay - (cy-ay)/dist_ac * dist_ab

    # f = extension of M past a: between(f,a,b)
    fx = ax - (bx-ax)/dist_ab * dist_ab
    fy = ay - (by-ay)/dist_ab * dist_ab

    # K = line(d, b)
    if math.hypot(ddx-bx, ddy-by) < 0.1:
        continue

    r = math.hypot(ddx-bx, ddy-by)
    pts = circle_circle_intersections(ddx, ddy, r, bx, by, r)
    if len(pts) < 2:
        continue

    # e = opposite K from a
    e0, e1 = pts
    ss0 = same_side(e0[0], e0[1], ax, ay, ddx, ddy, bx, by)
    ss1 = same_side(e1[0], e1[1], ax, ay, ddx, ddy, bx, by)

    if not ss0 and not on_line(e0[0], e0[1], ddx, ddy, bx, by):
        ex, ey = e0
    elif not ss1 and not on_line(e1[0], e1[1], ddx, ddy, bx, by):
        ex, ey = e1
    else:
        continue

    if on_line(ex, ey, ax, ay, bx, by) or on_line(ex, ey, ax, ay, cx, cy):
        continue
    if on_line(gx, gy, ax, ay, bx, by):
        continue
    if on_line(fx, fy, ax, ay, cx, cy):
        continue

    tested += 1

    # Test ¬ss(g,e,M) where M = line(a,b)
    if same_side(gx, gy, ex, ey, ax, ay, bx, by):
        violations_nss_ge_M += 1

    # Test ¬ss(f,e,N) where N = line(a,c)
    if same_side(fx, fy, ex, ey, ax, ay, cx, cy):
        violations_nss_fe_N += 1

print(f"Tested: {tested}")
print(f"¬ss(g,e,M) violations (ss=True when should be False): {violations_nss_ge_M}/{tested}")
print(f"¬ss(f,e,N) violations: {violations_nss_fe_N}/{tested}")
