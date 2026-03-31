"""Test various candidate axioms for the I.9 same-side gap.

Setup: 
- c,d are centers on line K, equal radii (cd=dc)
- e is circle-circle intersection, NOT on K
- a is a point NOT on K, on OPPOSITE side from e relative to K
- M is a line through BOTH a and one center (say through a and b where b is on K)
- We want: ss(e, d, M) where d is a center NOT on M

But let's test: ¬ss(e,a,K) ∧ ¬ss(a,d,M) (i.e., a opposite d rel M, because a is on M) 
Wait, a is ON M so ss is undefined for a.

Let me test the actual proof facts:
- K = line(d, b)
- M = line(a, b) 
- N = line(a, c) where c=d direction on N from a
- e on circle(d,db) and circle(b,bd), opposite K from a
- WANT: ss(e,c,M) and ss(e,b,N)

Test with the FULL I.9 configuration.
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
    if d < 1e-12 or d > r1 + r2 + 1e-12 or d < abs(r1 - r2) - 1e-12:
        return []
    a = (r1*r1 - r2*r2 + d*d) / (2*d)
    h2 = r1*r1 - a*a
    if h2 < -1e-12:
        return []
    h = math.sqrt(max(0, h2))
    mx, my = cx1 + a*dx/d, cy1 + a*dy/d
    px, py = -dy/d, dx/d
    return [(mx + h*px, my + h*py), (mx - h*px, my - h*py)]

random.seed(42)
tested = 0
v1 = 0  # ss(e,c,M) violations  
v2 = 0  # ss(e,b,N) violations

for _ in range(2_000_000):
    # a = vertex of angle
    ax, ay = random.uniform(-5, 5), random.uniform(-5, 5)
    # b = point on ray M from a
    bx, by = random.uniform(-5, 5), random.uniform(-5, 5)
    if math.hypot(bx-ax, by-ay) < 0.3:
        continue
    # c = point on ray N from a (different from M)
    cx, cy = random.uniform(-5, 5), random.uniform(-5, 5)
    if math.hypot(cx-ax, cy-ay) < 0.3:
        continue
    # M and N should be different (c not on M)
    if on_line(cx, cy, ax, ay, bx, by, tol=0.01):
        continue
    if on_line(bx, by, ax, ay, cx, cy, tol=0.01):
        continue

    # d = point on ray N from a at distance ab from a
    # (arm construction: d on N at radius ab)
    dist_ab = math.hypot(bx-ax, by-ay)
    dirN = math.atan2(cy-ay, cx-ax)
    # d should be on same side of a as c on N
    ddx = ax + dist_ab * math.cos(dirN)
    ddy = ay + dist_ab * math.sin(dirN)

    # K = line(d, b)
    if math.hypot(ddx-bx, ddy-by) < 0.1:
        continue

    # Circles: β centered d radius db, γ centered b radius bd
    r = math.hypot(ddx-bx, ddy-by)

    pts = circle_circle_intersections(ddx, ddy, r, bx, by, r)
    if len(pts) < 2:
        continue

    # Pick e on opposite side of K from a
    e0, e1 = pts
    ss0_a_K = same_side(e0[0], e0[1], ax, ay, ddx, ddy, bx, by)
    ss1_a_K = same_side(e1[0], e1[1], ax, ay, ddx, ddy, bx, by)

    if not ss0_a_K and not on_line(e0[0], e0[1], ddx, ddy, bx, by):
        ex, ey = e0
    elif not ss1_a_K and not on_line(e1[0], e1[1], ddx, ddy, bx, by):
        ex, ey = e1
    else:
        continue

    # Check e not on M, not on N
    if on_line(ex, ey, ax, ay, bx, by):
        continue
    if on_line(ex, ey, ax, ay, cx, cy):
        continue

    tested += 1

    # Check ss(e, c, M) where M = line(a, b)
    if not same_side(ex, ey, cx, cy, ax, ay, bx, by):
        v1 += 1

    # Check ss(e, b, N) where N = line(a, c)
    if not same_side(ex, ey, bx, by, ax, ay, cx, cy):
        v2 += 1

print(f"Tested: {tested}")
print(f"ss(e,c,M) violations: {v1}/{tested}")
print(f"ss(e,b,N) violations: {v2}/{tested}")
