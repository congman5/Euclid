"""Test with ss(d,c,M) constraint added.

Actually, I realize what makes I.9 special: d is on the SAME RAY from a as c.
Specifically, d is between a and c on line N (actually between(g,a,d) means
d is on the arm side, so d is between a and some extension).

Wait: in I.9, between(g,a,d) where g=extend, d=arm. So d is on the ray 
from a toward c (since d is on N on the arm side). And c is further along.

The key constraint: d is on the same side of M as c, AND a is on M.
Since on(a,M), on(b,M), and d,c are both NOT on M but ss(d,c,M)...

Let me test: equal radii circles, e opposite a rel K, AND ss(d,c,M) 
where c is ANY point same-side as d relative to M.
Actually the c doesn't matter for ss(e,d,M). Let me just check what 
additional constraint makes ss(e,d,M) true.

Hypothesis: maybe it's that a is on the SAME SIDE of K as d? Or inside 
the triangle? Or...

Let me check: in the violations (13%), what's the relationship between 
a and d relative to K?
"""
import random, math

def cross2d(ox, oy, ax, ay, bx, by):
    return (ax - ox) * (by - oy) - (ay - oy) * (bx - ox)

def same_side_val(px, py, qx, qy, lx1, ly1, lx2, ly2):
    cp = cross2d(lx1, ly1, lx2, ly2, px, py)
    cq = cross2d(lx1, ly1, lx2, ly2, qx, qy)
    return cp * cq

def same_side(px, py, qx, qy, lx1, ly1, lx2, ly2):
    return same_side_val(px, py, qx, qy, lx1, ly1, lx2, ly2) > 0

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

# Split by whether a and d are on same side of M
# Wait, a IS on M, so ss(a,d,M) is undefined. 
# Let me instead check ss(a,d,K) — are a and d on same side of K?
# In I.9: a is NOT on K. d IS on K. So ss(a,d,K) is undefined (d on K).

# What about: is a "between" d and b in some sense?
# In I.9: ad=ab. So triangle adb is isoceles. 

# Let me check: what % of violations have a inside β (dist(a,d)<db)?
tested_in = 0; v_in = 0
tested_out = 0; v_out = 0

for _ in range(3_000_000):
    dx, dy = random.uniform(-5, 5), random.uniform(-5, 5)
    bx, by = random.uniform(-5, 5), random.uniform(-5, 5)
    dist_db = math.hypot(dx-bx, dy-by)
    if dist_db < 0.3:
        continue

    r = dist_db
    pts = circle_circle_intersections(dx, dy, r, bx, by, r)
    if len(pts) < 2:
        continue

    ax, ay = random.uniform(-5, 5), random.uniform(-5, 5)
    if on_line(ax, ay, dx, dy, bx, by, tol=0.01):
        continue
    if math.hypot(ax-bx, ay-by) < 0.1:
        continue
    if on_line(dx, dy, ax, ay, bx, by, tol=0.01):
        continue

    for ex, ey in pts:
        if on_line(ex, ey, dx, dy, bx, by):
            continue
        if on_line(ex, ey, ax, ay, bx, by):
            continue
        if same_side(ex, ey, ax, ay, dx, dy, bx, by):
            continue  # want e opposite a rel K

        a_inside_beta = math.hypot(ax-dx, ay-dy) < r
        a_inside_gamma = math.hypot(ax-bx, ay-by) < r
        ss_ed = same_side(ex, ey, dx, dy, ax, ay, bx, by)

        if a_inside_beta and a_inside_gamma:
            tested_in += 1
            if not ss_ed:
                v_in += 1
        else:
            tested_out += 1
            if not ss_ed:
                v_out += 1

print(f"a inside BOTH: {v_in}/{tested_in} violations ({100*v_in/max(1,tested_in):.1f}%)")
print(f"a NOT inside both: {v_out}/{tested_out} violations ({100*v_out/max(1,tested_out):.1f}%)")
