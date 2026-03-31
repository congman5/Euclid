"""Verify: full I.9 construction => ss(e,d,M) and ss(e,c,M)."""
import random, math

def cross2d(ox, oy, ax, ay, bx, by):
    return (ax - ox) * (by - oy) - (ay - oy) * (bx - ox)

def same_side(px, py, qx, qy, lx1, ly1, lx2, ly2):
    c1 = cross2d(lx1, ly1, lx2, ly2, px, py)
    c2 = cross2d(lx1, ly1, lx2, ly2, qx, qy)
    return c1 * c2 > 0

def dist(x1, y1, x2, y2):
    return math.sqrt((x1-x2)**2 + (y1-y2)**2)

def circle_circle_intersect(cx1, cy1, r1, cx2, cy2, r2):
    d = dist(cx1, cy1, cx2, cy2)
    if d > r1 + r2 or d < abs(r1 - r2) or d < 1e-9:
        return []
    a = (r1*r1 - r2*r2 + d*d) / (2*d)
    h = math.sqrt(max(0, r1*r1 - a*a))
    mx = cx1 + a*(cx2-cx1)/d
    my = cy1 + a*(cy2-cy1)/d
    dx = h*(cy2-cy1)/d
    dy = -h*(cx2-cx1)/d
    return [(mx+dx, my+dy), (mx-dx, my-dy)]

violations_ecM = 0
violations_ebN = 0
tested = 0

for _ in range(3_000_000):
    ax, ay = random.uniform(-3, 3), random.uniform(-3, 3)
    angle = random.uniform(0.2, math.pi - 0.2)
    r = random.uniform(0.5, 3)

    # b on M (ray from a), c on N (ray from a at angle)
    t1 = random.uniform(0, 2*math.pi)
    bx, by = ax + r * 1.5 * math.cos(t1), ay + r * 1.5 * math.sin(t1)
    t2 = t1 + angle
    cx, cy = ax + r * 1.5 * math.cos(t2), ay + r * 1.5 * math.sin(t2)

    # d on arm of N (same side as c from a), on circle alpha (center a, radius r)
    # ad = ab = r, so d is at distance r from a on N direction
    ab = dist(ax, ay, bx, by)
    # Scale: d at distance ab from a in direction of c
    ac = dist(ax, ay, cx, cy)
    if ac < 1e-6: continue
    dx = ax + ab * (cx - ax) / ac
    dy = ay + ab * (cy - ay) / ac

    # Check d not on M
    cm = cross2d(ax, ay, bx, by, dx, dy)
    if abs(cm) < 0.01: continue

    # K = line(d, b)
    db = dist(dx, dy, bx, by)
    if db < 0.01: continue

    # Circles beta(d, db) and gamma(b, bd=db)
    pts = circle_circle_intersect(dx, dy, db, bx, by, db)
    if len(pts) < 2: continue

    # Pick e on opposite side of K from a
    e1, e2 = pts
    ck_a = cross2d(dx, dy, bx, by, ax, ay)
    ck_e1 = cross2d(dx, dy, bx, by, e1[0], e1[1])
    ck_e2 = cross2d(dx, dy, bx, by, e2[0], e2[1])

    if abs(ck_e1) < 1e-9 or abs(ck_e2) < 1e-9: continue

    if ck_a * ck_e1 < 0:
        ex, ey = e1
    elif ck_a * ck_e2 < 0:
        ex, ey = e2
    else:
        continue

    tested += 1

    # Check ss(e, c, M)
    if not same_side(ex, ey, cx, cy, ax, ay, bx, by):
        violations_ecM += 1

    # Check ss(e, b, N)
    if not same_side(ex, ey, bx, by, ax, ay, cx, cy):
        violations_ebN += 1

print(f"Tested: {tested}")
print(f"ss(e,c,M) violations: {violations_ecM}/{tested}")
print(f"ss(e,b,N) violations: {violations_ebN}/{tested}")
