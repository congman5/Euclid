"""C5 axiom — M goes through a and the OTHER center (d, not c).

Wait, in I.9: M = line(a,b). β has center d, γ has center b.
We want ss(e,d,M). M goes through a and b (= center of γ, not β).

So the axiom should be:
center(c,α) ∧ center(d,β) ∧ on(d,α) ∧ on(c,β) ∧ on(e,α) ∧ on(e,β) ∧
on(c,K) ∧ on(d,K) ∧ ¬on(a,K) ∧ ¬ss(e,a,K) ∧ ¬on(e,K) ∧
on(a,M) ∧ on(d,M) ∧ ¬on(c,M) ∧ ¬on(e,M)
→ ss(e,c,M)

i.e., M goes through a and center d, and we conclude ss(e,c,M) 
(e same side as the OTHER center c relative to M).

Actually wait — let me re-read the I.9 mapping:
- β center d, b on β → β = circle(d, radius db)  
- γ center b, d on γ → γ = circle(b, radius bd)
- K = line(d,b)
- e on β, on γ, opposite K from a
- M = line(a,b)  [a and b on M]
- Want: ss(e,d,M)  [e same side as d relative to M]

So M goes through a and center-of-γ (=b). Want ss(e, center-of-β (=d), M).

In the axiom with abstract names α,β, centers c,d:
- α center c, β center d
- M goes through a and c [c = center of α, like b = center of γ]
- Want ss(e, d, M) [d = center of β]

Let me retest with M through a and c (not d).
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
    a_v = (r1*r1 - r2*r2 + d*d) / (2*d)
    h2 = r1*r1 - a_v*a_v
    if h2 < -1e-12:
        return []
    h = math.sqrt(max(0, h2))
    mx, my = cx1 + a_v*ddx/d, cy1 + a_v*ddy/d
    px, py = -ddy/d, ddx/d
    return [(mx + h*px, my + h*py), (mx - h*px, my - h*py)]

random.seed(42)

# Test BOTH versions:
# Version A: M through a and c (center of α), conclude ss(e,d,M)
# Version B: M through a and d (center of β), conclude ss(e,c,M)

tested_a = 0; v_a = 0
tested_b = 0; v_b = 0

for _ in range(3_000_000):
    cx, cy = random.uniform(-5, 5), random.uniform(-5, 5)
    dx, dy = random.uniform(-5, 5), random.uniform(-5, 5)
    dist_cd = math.hypot(dx-cx, dy-cy)
    if dist_cd < 0.3:
        continue

    r = dist_cd
    pts = circle_circle_intersections(cx, cy, r, dx, dy, r)
    if len(pts) < 2:
        continue

    ax, ay = random.uniform(-5, 5), random.uniform(-5, 5)
    if on_line(ax, ay, cx, cy, dx, dy, tol=0.01):
        continue

    # Find e opposite a relative to K
    ex, ey = None, None
    for exx, eyy in pts:
        if on_line(exx, eyy, cx, cy, dx, dy):
            continue
        if same_side(exx, eyy, ax, ay, cx, cy, dx, dy):
            continue
        ex, ey = exx, eyy
        break
    if ex is None:
        continue

    # Version A: M = line(a, c)
    if math.hypot(ax-cx, ay-cy) > 0.1 and not on_line(dx, dy, ax, ay, cx, cy, tol=0.01):
        if not on_line(ex, ey, ax, ay, cx, cy):
            tested_a += 1
            if not same_side(ex, ey, dx, dy, ax, ay, cx, cy):
                v_a += 1

    # Version B: M = line(a, d)
    if math.hypot(ax-dx, ay-dy) > 0.1 and not on_line(cx, cy, ax, ay, dx, dy, tol=0.01):
        if not on_line(ex, ey, ax, ay, dx, dy):
            tested_b += 1
            if not same_side(ex, ey, cx, cy, ax, ay, dx, dy):
                v_b += 1

print(f"Version A (M thru a,c → ss(e,d,M)): {v_a}/{tested_a} ({100*v_a/max(1,tested_a):.2f}%)")
print(f"Version B (M thru a,d → ss(e,c,M)): {v_b}/{tested_b} ({100*v_b/max(1,tested_b):.2f}%)")
