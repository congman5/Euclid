"""Test axiom: two lines meeting at b, with a on M between b and ???

The KEY constraint I was missing: a must be on the SAME side of b 
on line M as g. Or rather, a must be between b and g projected onto M.

Actually let me test with the constraint that ss(a,g,K) is derived 
from between(g,a,d) and on(d,K), ¬on(a,K) via P2. This means 
there's a point d on K with between(g,a,d). So the segment g-d 
crosses BOTH lines (crosses K at some point, crosses ... hmm).

Let me try:
on(b,K) ∧ on(b,M) ∧ on(d,K) ∧ on(a,M) ∧ K≠M ∧
between(g,a,d) ∧ (so g,a,d collinear, a between g and d)
¬on(g,K) ∧ ¬on(g,M) ∧ ¬on(e,K) ∧ ¬on(e,M) ∧ ¬on(a,K) ∧
¬ss(e,a,K)
→ ¬ss(g,e,M)

This adds the between(g,a,d) with d on K, making g-a-d a segment 
from one side of K through a (on M) to d (on K).
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

def between(ax, ay, bx, by, cx, cy, tol=1e-9):
    """Is b between a and c?"""
    # b between a and c if collinear and a-b + b-c = a-c
    d_ab = math.hypot(bx-ax, by-ay)
    d_bc = math.hypot(cx-bx, cy-by)
    d_ac = math.hypot(cx-ax, cy-ay)
    return abs(d_ab + d_bc - d_ac) < tol

random.seed(42)
tested = 0
violations = 0

for _ in range(5_000_000):
    # Random b (intersection of K and M)
    bx, by = random.uniform(-3, 3), random.uniform(-3, 3)

    # K and M directions through b
    k_ang = random.uniform(0, math.pi)
    m_ang = random.uniform(0, math.pi)
    if abs(k_ang - m_ang) < 0.1 or abs(k_ang - m_ang - math.pi) < 0.1:
        continue

    # d on K, d≠b
    t_d = random.choice([-1,1]) * random.uniform(0.5, 5)
    dx = bx + t_d * math.cos(k_ang)
    dy = by + t_d * math.sin(k_ang)

    # a on M, a≠b, NOT on K
    t_a = random.choice([-1,1]) * random.uniform(0.5, 5)
    ax = bx + t_a * math.cos(m_ang)
    ay = by + t_a * math.sin(m_ang)
    if on_line(ax, ay, bx, by, dx, dy, tol=0.01):
        continue

    # g: between(g, a, d), so g is on the ray from d through a, past a
    # g = a + t*(a-d) for some t > 0
    t_g = random.uniform(0.3, 5)
    gx = ax + t_g * (ax - dx)
    gy = ay + t_g * (ay - dy)

    # Verify g not on K, not on M
    if on_line(gx, gy, bx, by, dx, dy, tol=0.01):
        continue
    if on_line(gx, gy, bx, by, ax, ay, tol=0.01):
        continue

    # e: random, not on K, not on M, ¬ss(e,a,K)
    ex, ey = random.uniform(-8, 8), random.uniform(-8, 8)
    if on_line(ex, ey, bx, by, dx, dy, tol=0.01):
        continue
    if on_line(ex, ey, bx, by, ax, ay, tol=0.01):
        continue
    if same_side(ex, ey, ax, ay, bx, by, dx, dy):
        continue  # need ¬ss(e,a,K)

    tested += 1

    if same_side(gx, gy, ex, ey, bx, by, ax, ay):
        violations += 1

print(f"Tested: {tested}, Violations: {violations}/{tested}")
if violations == 0:
    print("VALID")
else:
    print(f"INVALID — {100*violations/tested:.2f}%")
