"""Final verification of C5 axiom:

center(c,α) ∧ center(d,β) ∧ on(d,α) ∧ on(c,β) ∧ on(e,α) ∧ on(e,β) ∧
on(c,K) ∧ on(d,K) ∧ ¬on(a,K) ∧ ¬ss(e,a,K) ∧ ¬on(e,K) ∧
on(a,M) ∧ on(c,M) ∧ ¬on(d,M) ∧ ¬on(e,M)
→ ss(e,d,M)

With COMPLETELY random c, d (centers), random a, random M through a and c.
Circles have equal radii = dist(c,d).
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
tested = 0
violations = 0

for _ in range(5_000_000):
    # Random centers c, d
    cx, cy = random.uniform(-5, 5), random.uniform(-5, 5)
    dx, dy = random.uniform(-5, 5), random.uniform(-5, 5)
    dist_cd = math.hypot(dx-cx, dy-cy)
    if dist_cd < 0.3:
        continue

    # Equal radii = dist(c,d) (reciprocal circles)
    r = dist_cd
    pts = circle_circle_intersections(cx, cy, r, dx, dy, r)
    if len(pts) < 2:
        continue

    # Random a, NOT on K = line(c,d)
    ax, ay = random.uniform(-5, 5), random.uniform(-5, 5)
    if on_line(ax, ay, cx, cy, dx, dy, tol=0.01):
        continue

    # M = line(a, c); check d not on M
    if math.hypot(ax-cx, ay-cy) < 0.1:
        continue
    if on_line(dx, dy, ax, ay, cx, cy, tol=0.01):
        continue

    # e = intersection point opposite K from a
    for ex, ey in pts:
        if on_line(ex, ey, cx, cy, dx, dy):
            continue
        if same_side(ex, ey, ax, ay, cx, cy, dx, dy):
            continue  # want ¬ss(e,a,K)
        if on_line(ex, ey, ax, ay, cx, cy):
            continue  # want ¬on(e,M)

        tested += 1
        if not same_side(ex, ey, dx, dy, ax, ay, cx, cy):
            violations += 1
        break

print(f"Tested: {tested}, Violations: {violations}/{tested}")
if violations == 0:
    print("C5 AXIOM VALID — 0 violations")
else:
    print(f"C5 AXIOM INVALID — {100*violations/tested:.2f}%")
