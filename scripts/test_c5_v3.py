"""Test C5 with the key constraint: a is on M.

center(d,α) ∧ center(b,β) ∧ on(e,α) ∧ on(e,β) ∧
on(d,K) ∧ on(b,K) ∧ ¬on(a,K) ∧ ¬ss(e,a,K) ∧ ¬on(e,K) ∧
on(a,M) ∧ on(b,M) ∧ ¬on(d,M) ∧ ¬on(e,M)
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

for _ in range(3_000_000):
    # Random d (center of α), b (center of β)
    dx, dy = random.uniform(-5, 5), random.uniform(-5, 5)
    bx, by = random.uniform(-5, 5), random.uniform(-5, 5)
    if math.hypot(dx-bx, dy-by) < 0.2:
        continue

    # K = line(d, b)
    # Random radii
    r1 = random.uniform(0.5, 5)
    r2 = random.uniform(0.5, 5)
    dist_db = math.hypot(dx-bx, dy-by)
    if r1 + r2 < dist_db or abs(r1 - r2) > dist_db:
        continue

    pts = circle_circle_intersections(dx, dy, r1, bx, by, r2)
    if len(pts) < 2:
        continue

    # a = random point NOT on K
    ax, ay = random.uniform(-5, 5), random.uniform(-5, 5)
    if on_line(ax, ay, dx, dy, bx, by, tol=0.01):
        continue

    # M = line(a, b) — a and b are on M
    # Check d NOT on M
    if on_line(dx, dy, ax, ay, bx, by, tol=0.01):
        continue

    # Pick e on opposite side of K from a
    e0, e1 = pts
    ss0 = same_side(e0[0], e0[1], ax, ay, dx, dy, bx, by)
    ss1 = same_side(e1[0], e1[1], ax, ay, dx, dy, bx, by)

    if not ss0 and not on_line(e0[0], e0[1], dx, dy, bx, by):
        ex, ey = e0
    elif not ss1 and not on_line(e1[0], e1[1], dx, dy, bx, by):
        ex, ey = e1
    else:
        continue

    # Check e NOT on M
    if on_line(ex, ey, ax, ay, bx, by):
        continue

    tested += 1

    if not same_side(ex, ey, dx, dy, ax, ay, bx, by):
        violations += 1

print(f"Tested: {tested}, Violations: {violations}/{tested}")
if violations == 0:
    print("VALID — 0 violations")
else:
    pct = 100*violations/tested
    print(f"INVALID — {pct:.1f}% violations")
