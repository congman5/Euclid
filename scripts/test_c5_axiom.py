"""Numerical test for proposed C5 axiom:
center(c,α) ∧ center(d,β) ∧ on(e,α) ∧ on(e,β) ∧
on(c,K) ∧ on(d,K) ∧ on(c,M) ∧ ¬on(d,M) ∧ ¬on(e,K) ∧ ¬on(e,M)
→ ss(e,d,M)
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
    dx, dy = cx2 - cx1, cy2 - cy1
    d = math.hypot(dx, dy)
    if d < 1e-12 or d > r1 + r2 or d < abs(r1 - r2):
        return []
    a = (r1*r1 - r2*r2 + d*d) / (2*d)
    h2 = r1*r1 - a*a
    if h2 < 0:
        return []
    h = math.sqrt(max(0, h2))
    mx, my = cx1 + a*dx/d, cy1 + a*dy/d
    px, py = -dy/d, dx/d
    return [(mx + h*px, my + h*py), (mx - h*px, my - h*py)]

random.seed(42)
tested = 0
violations = 0

for _ in range(3_000_000):
    # Random centers c, d
    cx, cy = random.uniform(-10, 10), random.uniform(-10, 10)
    dx, dy = random.uniform(-10, 10), random.uniform(-10, 10)
    if math.hypot(dx - cx, dy - cy) < 0.1:
        continue

    # Random radii that ensure intersection
    dist_cd = math.hypot(dx - cx, dy - cy)
    r1 = random.uniform(dist_cd * 0.3, dist_cd * 1.5)
    r2 = random.uniform(dist_cd * 0.3, dist_cd * 1.5)
    if r1 + r2 < dist_cd or abs(r1 - r2) > dist_cd:
        continue

    pts = circle_circle_intersections(cx, cy, r1, dx, dy, r2)
    if len(pts) < 2:
        continue

    # e is one of the two intersection points
    e = pts[random.randint(0, 1)]
    ex, ey = e

    # K = line through c, d (centers)
    # Check ¬on(e, K)
    if on_line(ex, ey, cx, cy, dx, dy):
        continue

    # M = random line through c (not through d)
    # Pick a random direction for M through c
    angle = random.uniform(0, math.pi)
    mx2, my2 = cx + math.cos(angle), cy + math.sin(angle)

    # Check ¬on(d, M)
    if on_line(dx, dy, cx, cy, mx2, my2):
        continue

    # Check ¬on(e, M)
    if on_line(ex, ey, cx, cy, mx2, my2):
        continue

    tested += 1

    # Check ss(e, d, M)
    if not same_side(ex, ey, dx, dy, cx, cy, mx2, my2):
        violations += 1

print(f"Tested: {tested}, Violations: {violations}/{tested}")
if violations == 0:
    print("C5 axiom is VALID (0 violations)")
else:
    print(f"C5 axiom has {violations} violations — NOT VALID")
