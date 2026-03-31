"""Test with the KEY I.9 structural constraint:
- on(a,M), on(b,M), on(a,N), on(d,N) 
- K = line(d,b)
- Equal radii: both circles have radius db
- e = circle intersection opposite K from a
- ¬on(e,M), ¬on(e,N)

Test ss(e,d,M) and ss(e,b,N).

This is EXACTLY the I.9 setup: a is vertex of angle bac (with d on ray ac).
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
tested = 0; v_edM = 0; v_ebN = 0

for _ in range(3_000_000):
    ax, ay = random.uniform(-5, 5), random.uniform(-5, 5)
    bx, by = random.uniform(-5, 5), random.uniform(-5, 5)
    if math.hypot(bx-ax, by-ay) < 0.3:
        continue

    # d on ray from a, NOT same direction as b, at distance ab from a 
    # (but arbitrary direction — this is key: d is NOT necessarily toward c)
    angle_d = random.uniform(0, 2*math.pi)
    dist_ab = math.hypot(bx-ax, by-ay)
    dx = ax + dist_ab * math.cos(angle_d)
    dy = ay + dist_ab * math.sin(angle_d)

    # N = line(a,d)
    # M = line(a,b)
    # These should be different
    if on_line(dx, dy, ax, ay, bx, by, tol=0.01):
        continue  # d on M, so N=M
    if on_line(bx, by, ax, ay, dx, dy, tol=0.01):
        continue

    # K = line(d,b)
    if math.hypot(dx-bx, dy-by) < 0.1:
        continue
    # a should NOT be on K
    if on_line(ax, ay, dx, dy, bx, by, tol=0.01):
        continue

    r = math.hypot(dx-bx, dy-by)
    pts = circle_circle_intersections(dx, dy, r, bx, by, r)
    if len(pts) < 2:
        continue

    # e = opposite K from a
    e0, e1 = pts
    found = False
    for ex, ey in [e0, e1]:
        if on_line(ex, ey, dx, dy, bx, by):
            continue
        if same_side(ex, ey, ax, ay, dx, dy, bx, by):
            continue
        if on_line(ex, ey, ax, ay, bx, by):
            continue
        if on_line(ex, ey, ax, ay, dx, dy):
            continue
        found = True
        break

    if not found:
        continue

    tested += 1
    if not same_side(ex, ey, dx, dy, ax, ay, bx, by):
        v_edM += 1
    if not same_side(ex, ey, bx, by, ax, ay, dx, dy):
        v_ebN += 1

print(f"Tested: {tested}")
print(f"ss(e,d,M) violations: {v_edM}/{tested} ({100*v_edM/max(1,tested):.2f}%)")
print(f"ss(e,b,N) violations: {v_ebN}/{tested} ({100*v_ebN/max(1,tested):.2f}%)")
