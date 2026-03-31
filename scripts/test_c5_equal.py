"""Numerical test for C5 axiom with EQUAL radii constraint:
center(c,α) ∧ center(d,β) ∧ on(d,α) ∧ on(c,β) ∧ on(e,α) ∧ on(e,β) ∧
on(c,K) ∧ on(d,K) ∧ on(c,M) ∧ ¬on(d,M) ∧ ¬on(e,K) ∧ ¬on(e,M)
→ ss(e,d,M)

i.e., both circles have radius = dist(c,d), so r1=r2=cd.
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
    cx, cy = random.uniform(-10, 10), random.uniform(-10, 10)
    dx, dy = random.uniform(-10, 10), random.uniform(-10, 10)
    dist_cd = math.hypot(dx - cx, dy - cy)
    if dist_cd < 0.1:
        continue

    # Equal radii: r1 = r2 = dist(c,d)
    r = dist_cd

    pts = circle_circle_intersections(cx, cy, r, dx, dy, r)
    if len(pts) < 2:
        continue

    e = pts[random.randint(0, 1)]
    ex, ey = e

    if on_line(ex, ey, cx, cy, dx, dy):
        continue

    # M = random line through c
    angle = random.uniform(0, math.pi)
    mx2, my2 = cx + math.cos(angle), cy + math.sin(angle)

    if on_line(dx, dy, cx, cy, mx2, my2):
        continue
    if on_line(ex, ey, cx, cy, mx2, my2):
        continue

    tested += 1

    if not same_side(ex, ey, dx, dy, cx, cy, mx2, my2):
        violations += 1

print(f"Tested: {tested}, Violations: {violations}/{tested}")
if violations == 0:
    print("C5 axiom (equal radii) is VALID")
else:
    print(f"C5 axiom (equal radii) has {violations} violations")
