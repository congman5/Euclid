"""C5 with equidistant constraint: dist(a,c) = dist(a,d) = dist(c,d).

Actually in I.9: dist(a,d) = dist(a,b) = radius of α. But dist(a,d) is 
NOT necessarily equal to dist(d,b) = dist(c,d).

What IS true: dist(a,d) = dist(a,b) (= dist(a,c) in abstract). So a is 
equidistant from both centers. Let me test that.
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
tested = 0; violations = 0

for _ in range(5_000_000):
    cx, cy = random.uniform(-5, 5), random.uniform(-5, 5)
    dx, dy = random.uniform(-5, 5), random.uniform(-5, 5)
    dist_cd = math.hypot(dx-cx, dy-cy)
    if dist_cd < 0.3:
        continue

    r = dist_cd
    pts = circle_circle_intersections(cx, cy, r, dx, dy, r)
    if len(pts) < 2:
        continue

    # a equidistant from c and d (on perpendicular bisector of cd)
    # AND not on K = line(c,d)
    mx, my = (cx+dx)/2, (cy+dy)/2  # midpoint of cd
    perp_x, perp_y = -(dy-cy), dx-cx  # perpendicular direction
    plen = math.hypot(perp_x, perp_y)
    if plen < 1e-12:
        continue
    perp_x /= plen; perp_y /= plen
    t = random.choice([-1,1]) * random.uniform(0.3, 5)
    ax = mx + t * perp_x
    ay = my + t * perp_y

    if on_line(ax, ay, cx, cy, dx, dy, tol=0.01):
        continue

    # M = line(a, c)
    if math.hypot(ax-cx, ay-cy) < 0.1:
        continue
    if on_line(dx, dy, ax, ay, cx, cy, tol=0.01):
        continue

    ex, ey = None, None
    for exx, eyy in pts:
        if on_line(exx, eyy, cx, cy, dx, dy):
            continue
        if same_side(exx, eyy, ax, ay, cx, cy, dx, dy):
            continue
        if on_line(exx, eyy, ax, ay, cx, cy):
            continue
        ex, ey = exx, eyy
        break
    if ex is None:
        continue

    tested += 1
    if not same_side(ex, ey, dx, dy, ax, ay, cx, cy):
        violations += 1

print(f"Tested: {tested}, Violations: {violations}/{tested}")
if violations == 0:
    print("VALID with equidistant constraint")
else:
    print(f"INVALID — {100*violations/tested:.2f}%")
