"""Minimal axiom test:

on(a,K) ∧ on(b,K) ∧ on(a,M) ∧ on(c,M) ∧ ¬on(a,L) ∧ ¬on(b,M) ∧
¬on(d,K) ∧ ¬on(d,M) ∧ ¬on(d,L) ∧
¬ss(d,a,K)... 

No, let me try the ACTUAL Pasch/separation theorem.

Pasch's axiom (plane separation form):
If a line L separates points p,q (¬ss(p,q,L)) and another line M 
passes through a point on L and p is on one side of M, then...

Actually, the theorem I want is:

THEOREM (Plane separation by two intersecting lines):
If L and M intersect at point a, and p is on opposite side of L from q,
and p is NOT on M, and q is NOT on M, then either:
(a) p and q are on the same side of M, or
(b) p and q are on opposite sides of M.
Both are possible in general, so there's no universal implication.

The key special thing in I.9 is that g and e are constrained by the circles.

Let me try a MUCH more targeted axiom. In the I.9 proof:
- between(g,a,d) (g and d on opposite sides of a on line N)
- on(a,M), on(b,M) (M is a line through a and b)
- on(d,K), on(b,K) (K is a line through d and b)
- ¬ss(e,a,K) (e is opposite a relative to K)
- ¬on(e,M), ¬on(e,K), ¬on(g,M), ¬on(g,K)

Want: ¬ss(g,e,M)

The key is: K passes through b (which is on M). So K and M intersect at b.
g is on the same side of K as a (from P2: between(d,a,g) ∧ on(d,K) → ss(a,g,K)).
e is on opposite side of K from a, so ¬ss(e,g,K).
Both g and e are not on K and not on M.

Now, M passes through a and b. K passes through d and b. They intersect at b.

g is on same side of K as a (proved).
What side of M is g on? between(g,a,c), on(a,M) → ¬ss(g,c,M).
So g is on opposite side of M from c.

e is on opposite side of K from a.
What side of M is e on? This is what we want to determine.

Claim: e is on same side of M as c (and d), i.e., opposite side from g.
This would give ¬ss(g,e,M).

Intuitively: e is "below" K (opposite from a), and c,d are "above" M 
(from ss(d,c,M)). The angle at b between K and M determines the quadrant...

Actually, let me test a GENERAL plane-geometry axiom about lines meeting at a point:

AXIOM (Crossbar variant):
on(a,L) ∧ on(a,M) ∧ a≠b ∧ on(b,L) ∧ on(b,M) ∧ L≠M — wait, this would
mean a and b on both L and M, forcing L=M. That's wrong.

K and M meet at b (both pass through b), not at a. Let me reconsider.

K passes through b and d.
M passes through a and b.
They meet at b.

Let me test:
on(b,K) ∧ on(b,M) ∧ K≠M ∧
¬on(p,K) ∧ ¬on(p,M) ∧ ¬on(q,K) ∧ ¬on(q,M) ∧
¬ss(p,q,K) ∧ ss(p,r,K) (for some r on M, r≠b)
→ ... what?

This is getting too abstract. Let me just test the EXACT axiom I need as a 
"Pasch for triangle with vertex on two lines":

on(b,K) ∧ on(b,M) ∧ K≠M ∧ 
on(a,M) ∧ a≠b ∧ ¬on(a,K) ∧
¬on(g,K) ∧ ¬on(g,M) ∧ ¬on(e,K) ∧ ¬on(e,M) ∧
ss(a,g,K) ∧ ¬ss(e,a,K) ∧ between(g,a,d) ∧ on(d,K)
→ ¬ss(g,e,M)

But even more general: just test without the between and d.

AXIOM CANDIDATE:
on(b,K) ∧ on(b,M) ∧ K≠M ∧ on(a,M) ∧ a≠b ∧ ¬on(a,K) ∧
¬on(g,K) ∧ ¬on(g,M) ∧ ¬on(e,K) ∧ ¬on(e,M) ∧
ss(a,g,K) ∧ ¬ss(e,a,K)
→ ¬ss(g,e,M)

English: K and M meet at b. a is on M but not K. g is in a's half-plane 
of K. e is in the opposite half-plane of K from a. All off both lines.
→ g and e are on opposite sides of M.

This is essentially: if two points are on opposite sides of K, and one 
is on the same side as a point on M (specifically a), then they're on 
opposite sides of M (which passes through b, the intersection of K and M).

This is a standard consequence of Pasch's axiom! Let me test it.
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

random.seed(42)
tested = 0
violations = 0

for _ in range(5_000_000):
    # b = intersection point of K and M
    bx, by = random.uniform(-5, 5), random.uniform(-5, 5)

    # K direction (through b)
    k_angle = random.uniform(0, math.pi)
    kx2 = bx + math.cos(k_angle)
    ky2 = by + math.sin(k_angle)

    # M direction (through b), different from K
    m_angle = random.uniform(0, math.pi)
    if abs(m_angle - k_angle) < 0.05 or abs(m_angle - k_angle - math.pi) < 0.05:
        continue
    mx2 = bx + math.cos(m_angle)
    my2 = by + math.sin(m_angle)

    # a on M, not on K, a≠b
    t_a = random.choice([-1, 1]) * random.uniform(0.5, 5)
    ax = bx + t_a * math.cos(m_angle)
    ay = by + t_a * math.sin(m_angle)

    if on_line(ax, ay, bx, by, kx2, ky2, tol=0.01):
        continue

    # g: not on K, not on M, ss(a,g,K) 
    gx, gy = random.uniform(-8, 8), random.uniform(-8, 8)
    if on_line(gx, gy, bx, by, kx2, ky2, tol=0.01):
        continue
    if on_line(gx, gy, bx, by, mx2, my2, tol=0.01):
        continue
    if not same_side(ax, ay, gx, gy, bx, by, kx2, ky2):
        continue

    # e: not on K, not on M, ¬ss(e,a,K)
    ex, ey = random.uniform(-8, 8), random.uniform(-8, 8)
    if on_line(ex, ey, bx, by, kx2, ky2, tol=0.01):
        continue
    if on_line(ex, ey, bx, by, mx2, my2, tol=0.01):
        continue
    if same_side(ex, ey, ax, ay, bx, by, kx2, ky2):
        continue  # need ¬ss(e,a,K)

    tested += 1

    # Check ¬ss(g,e,M) — want this to be TRUE, so ss(g,e,M) should be False
    if same_side(gx, gy, ex, ey, bx, by, mx2, my2):
        violations += 1

print(f"Tested: {tested}, Violations: {violations}/{tested}")
if violations == 0:
    print("VALID — ¬ss(g,e,M) always holds")
else:
    print(f"INVALID — {100*violations/tested:.2f}%")
