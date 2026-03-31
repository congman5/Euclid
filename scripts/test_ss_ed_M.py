"""Verify: e opposite K from a, K through d,b, M through a,b => ss(e,d,M)."""
import random, math

def cross2d(ox, oy, ax, ay, bx, by):
    return (ax - ox) * (by - oy) - (ay - oy) * (bx - ox)

def same_side(px, py, qx, qy, lx1, ly1, lx2, ly2):
    c1 = cross2d(lx1, ly1, lx2, ly2, px, py)
    c2 = cross2d(lx1, ly1, lx2, ly2, qx, qy)
    return c1 * c2 > 0

violations = 0
tested = 0
for _ in range(2_000_000):
    ax, ay = random.uniform(-5, 5), random.uniform(-5, 5)
    bx, by = random.uniform(-5, 5), random.uniform(-5, 5)
    if abs(ax - bx) + abs(ay - by) < 0.01: continue
    dx, dy = random.uniform(-5, 5), random.uniform(-5, 5)
    # d must not be on M (line a-b)
    c = cross2d(ax, ay, bx, by, dx, dy)
    if abs(c) < 0.01: continue
    # K = line(d, b)
    # e on opposite side of K from a, and not on K
    ex, ey = random.uniform(-5, 5), random.uniform(-5, 5)
    # check e opposite K from a
    ck_a = cross2d(dx, dy, bx, by, ax, ay)
    ck_e = cross2d(dx, dy, bx, by, ex, ey)
    if abs(ck_e) < 0.01: continue  # e on K
    if ck_a * ck_e > 0: continue  # same side, skip (want opposite)
    # Now: e is on opposite side of K from a
    # Check ss(e, d, M): e and d on same side of M (line a-b)
    tested += 1
    if not same_side(ex, ey, dx, dy, ax, ay, bx, by):
        violations += 1

print(f"Tested: {tested}, Violations: {violations}")
print(f"ss(e,d,M) is {'ALWAYS TRUE' if violations == 0 else f'{violations}/{tested} violations'}")
