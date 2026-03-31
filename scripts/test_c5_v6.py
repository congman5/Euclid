"""Test: What makes ss(e,d,M) true in I.9?

Core facts:
- center(d,β), on(b,β)  → β has center d, b is on it, radius=db
- center(b,γ), on(d,γ)  → γ has center b, d is on it, radius=bd
- So β and γ have EQUAL radii = dist(d,b)
- on(e,β), on(e,γ) → e is on both circles
- on(d,K), on(b,K) → K = line through d,b (the "center line")
- ¬on(e,K) → e is not on K
- on(a,M), on(b,M) → M passes through a and b
- ¬on(d,M) → d not on M
- ¬on(e,M) → e not on M
- ¬ss(e,a,K) → e and a on opposite sides of K

Let me test: does adding ¬ss(e,a,K) to the circle setup guarantee ss(e,d,M)?
Or does it work even WITHOUT ¬ss(e,a,K)?

Test 1: Just circles + lines, NO side constraint on e
Test 2: With ¬ss(e,a,K)
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
    a = (r1*r1 - r2*r2 + d*d) / (2*d)
    h2 = r1*r1 - a*a
    if h2 < -1e-12:
        return []
    h = math.sqrt(max(0, h2))
    mx, my = cx1 + a*ddx/d, cy1 + a*ddy/d
    px, py = -ddy/d, ddx/d
    return [(mx + h*px, my + h*py), (mx - h*px, my - h*py)]

random.seed(42)

# Test both intersection points (not just opposite-a)
tested_any = 0
violations_any = 0
tested_opp = 0  
violations_opp = 0

for _ in range(3_000_000):
    dx, dy = random.uniform(-5, 5), random.uniform(-5, 5)
    bx, by = random.uniform(-5, 5), random.uniform(-5, 5)
    dist_db = math.hypot(dx-bx, dy-by)
    if dist_db < 0.3:
        continue

    # Equal radii: r = dist(d,b) — "each center on the other's circle"
    r = dist_db
    pts = circle_circle_intersections(dx, dy, r, bx, by, r)
    if len(pts) < 2:
        continue

    # a: random point on a line through b (M), not on K=line(d,b)
    ax, ay = random.uniform(-5, 5), random.uniform(-5, 5)
    if on_line(ax, ay, dx, dy, bx, by, tol=0.01):
        continue
    if math.hypot(ax-bx, ay-by) < 0.1:
        continue

    # M = line(a,b). Check d not on M
    if on_line(dx, dy, ax, ay, bx, by, tol=0.01):
        continue

    for idx, (ex, ey) in enumerate(pts):
        if on_line(ex, ey, dx, dy, bx, by):
            continue
        if on_line(ex, ey, ax, ay, bx, by):
            continue

        tested_any += 1
        ss_ed = same_side(ex, ey, dx, dy, ax, ay, bx, by)
        if not ss_ed:
            violations_any += 1

        # With opposite-side constraint
        if not same_side(ex, ey, ax, ay, dx, dy, bx, by):
            tested_opp += 1
            if not ss_ed:
                violations_opp += 1

print(f"Test 1 (any e): {violations_any}/{tested_any} violations ({100*violations_any/max(1,tested_any):.1f}%)")
print(f"Test 2 (e opp a): {violations_opp}/{tested_opp} violations ({100*violations_opp/max(1,tested_opp):.1f}%)")
