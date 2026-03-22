"""
Build geometrically accurate canvas data for each solved proposition.

Each canvas reflects the complete construction from Euclid's Elements,
with computed coordinates for all points and the full set of geometric
objects (segments, circles, rays, angle marks, equality groups).
"""
import json
import math
import os

SOLVED_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "solved_proofs")

# Color palette
BLUE = "#2d70b3"
RED = "#cc3333"
GREEN = "#2e8b57"
PURPLE = "#8b5cf6"
ORANGE = "#e67e22"
BLACK = "#333333"


def _circle_intersect(cx1, cy1, cx2, cy2, r1, r2, top=True):
    """Find intersection of two circles.
    top=True gives visually upper point (smaller y in screen coords)."""
    dx, dy = cx2 - cx1, cy2 - cy1
    d = math.sqrt(dx*dx + dy*dy)
    a = (r1*r1 - r2*r2 + d*d) / (2*d)
    h = math.sqrt(max(0, r1*r1 - a*a))
    mx, my = cx1 + a*dx/d, cy1 + a*dy/d
    px, py = -dy/d * h, dx/d * h
    # Two candidates
    y1 = my + py
    y2 = my - py
    if top:
        # Return the one with smaller y (visually higher)
        if y1 <= y2:
            return mx + px, y1
        else:
            return mx - px, y2
    else:
        if y1 >= y2:
            return mx + px, y1
        else:
            return mx - px, y2


def _midpoint(x1, y1, x2, y2):
    return (x1+x2)/2, (y1+y2)/2


def _dist(x1, y1, x2, y2):
    return math.sqrt((x2-x1)**2 + (y2-y1)**2)


def _point_on_line_at_dist(x1, y1, x2, y2, dist_from_1):
    """Point on line from (x1,y1) through (x2,y2) at given distance from (x1,y1)."""
    d = _dist(x1, y1, x2, y2)
    if d < 1e-9:
        return x1, y1
    t = dist_from_1 / d
    return x1 + t*(x2-x1), y1 + t*(y2-y1)


def _line_circle_intersect(x1, y1, x2, y2, cx, cy, r, far=True):
    """Intersect line through (x1,y1)-(x2,y2) with circle centered at (cx,cy)."""
    dx, dy = x2-x1, y2-y1
    fx, fy = x1-cx, y1-cy
    a = dx*dx + dy*dy
    b = 2*(fx*dx + fy*dy)
    c = fx*fx + fy*fy - r*r
    disc = b*b - 4*a*c
    if disc < 0:
        disc = 0
    sd = math.sqrt(disc)
    t1 = (-b - sd) / (2*a)
    t2 = (-b + sd) / (2*a)
    t = t2 if far else t1
    return x1 + t*dx, y1 + t*dy


def canvas_i1():
    """I.1: Construct equilateral triangle on segment AB."""
    ax, ay = 200, 300
    bx, by = 450, 300
    r = _dist(ax, ay, bx, by)
    cx, cy = _circle_intersect(ax, ay, bx, by, r, r, top=True)
    return {
        "points": [
            {"label": "A", "x": ax, "y": ay},
            {"label": "B", "x": bx, "y": by},
            {"label": "C", "x": round(cx, 2), "y": round(cy, 2)},
        ],
        "segments": [
            {"from": "A", "to": "B", "color": BLUE},
            {"from": "A", "to": "C", "color": BLUE},
            {"from": "C", "to": "B", "color": BLUE},
        ],
        "rays": [],
        "circles": [
            {"center": "A", "radius": r, "radius_point": "B", "color": BLUE},
            {"center": "B", "radius": r, "radius_point": "A", "color": RED},
        ],
        "angleMarks": [],
        "equalityGroups": [
            [1, [["A", "B"], ["A", "C"], ["B", "C"]]]
        ]
    }


def canvas_i2():
    """I.2: Place at A a segment equal to BC."""
    ax, ay = 200, 250
    bx, by = 350, 350
    cx, cy = 480, 350
    # Construct equilateral triangle ABD (I.1)
    r_ab = _dist(ax, ay, bx, by)
    dx, dy = _circle_intersect(ax, ay, bx, by, r_ab, r_ab, top=True)
    # Circle centered B, radius BC
    r_bc = _dist(bx, by, cx, cy)
    # Extend DB to meet circle: G on circle(B, BC), far side from D
    gx, gy = _line_circle_intersect(dx, dy, bx, by, bx, by, r_bc, far=True)
    # Circle centered D, radius DG
    r_dg = _dist(dx, dy, gx, gy)
    # Extend DA to meet circle(D, DG): F
    fx, fy = _line_circle_intersect(dx, dy, ax, ay, dx, dy, r_dg, far=True)
    return {
        "points": [
            {"label": "A", "x": ax, "y": ay},
            {"label": "B", "x": bx, "y": by},
            {"label": "C", "x": cx, "y": cy},
            {"label": "D", "x": round(dx, 2), "y": round(dy, 2)},
            {"label": "G", "x": round(gx, 2), "y": round(gy, 2)},
            {"label": "F", "x": round(fx, 2), "y": round(fy, 2)},
        ],
        "segments": [
            {"from": "B", "to": "C", "color": BLUE},
            {"from": "A", "to": "B", "color": BLACK},
            {"from": "A", "to": "D", "color": BLACK},
            {"from": "B", "to": "D", "color": BLACK},
            {"from": "A", "to": "F", "color": GREEN},
        ],
        "rays": [
            {"from": "D", "through": "A", "color": RED},
            {"from": "D", "through": "B", "color": RED},
        ],
        "circles": [
            {"center": "B", "radius": r_bc, "radius_point": "C", "color": BLUE},
            {"center": "D", "radius": r_dg, "radius_point": "G", "color": RED},
        ],
        "angleMarks": [],
        "equalityGroups": [
            [1, [["A", "F"], ["B", "C"]]]
        ]
    }


def canvas_i3():
    """I.3: Cut off from the greater a segment equal to the less."""
    ax, ay = 150, 300
    bx, by = 500, 300
    cx, cy = 200, 420
    dx, dy = 320, 420
    # By I.2, place at A a segment AF = CD
    r_cd = _dist(cx, cy, dx, dy)
    r_ab = _dist(ax, ay, bx, by)
    # Circle centered A, radius AF = CD
    # E is on AB at distance CD from A
    ex, ey = _point_on_line_at_dist(ax, ay, bx, by, r_cd)
    # F is on the circle at angle pointing up
    fx, fy = ax, ay - r_cd
    return {
        "points": [
            {"label": "A", "x": ax, "y": ay},
            {"label": "B", "x": bx, "y": by},
            {"label": "C", "x": cx, "y": cy},
            {"label": "D", "x": dx, "y": dy},
            {"label": "F", "x": round(fx, 2), "y": round(fy, 2)},
            {"label": "E", "x": round(ex, 2), "y": round(ey, 2)},
        ],
        "segments": [
            {"from": "A", "to": "B", "color": BLUE},
            {"from": "C", "to": "D", "color": BLUE},
            {"from": "A", "to": "F", "color": GREEN},
            {"from": "A", "to": "E", "color": RED},
        ],
        "rays": [],
        "circles": [
            {"center": "A", "radius": r_cd, "radius_point": "F", "color": RED},
        ],
        "angleMarks": [],
        "equalityGroups": [
            [1, [["A", "E"], ["C", "D"], ["A", "F"]]]
        ]
    }


def canvas_i4():
    """I.4: SAS congruence. Two triangles with matching sides and included angle."""
    # Triangle ABC
    ax, ay = 120, 150
    bx, by = 50, 380
    cx, cy = 280, 380
    # Triangle DEF (congruent, shifted right)
    dx, dy = 420, 150
    ex, ey = 350, 380
    fx, fy = 580, 380
    return {
        "points": [
            {"label": "A", "x": ax, "y": ay},
            {"label": "B", "x": bx, "y": by},
            {"label": "C", "x": cx, "y": cy},
            {"label": "D", "x": dx, "y": dy},
            {"label": "E", "x": ex, "y": ey},
            {"label": "F", "x": fx, "y": fy},
        ],
        "segments": [
            {"from": "A", "to": "B", "color": BLUE},
            {"from": "A", "to": "C", "color": BLUE},
            {"from": "B", "to": "C", "color": BLUE},
            {"from": "D", "to": "E", "color": RED},
            {"from": "D", "to": "F", "color": RED},
            {"from": "E", "to": "F", "color": RED},
        ],
        "rays": [],
        "circles": [],
        "angleMarks": [
            {"from": "B", "vertex": "A", "to": "C", "is_right": False},
            {"from": "E", "vertex": "D", "to": "F", "is_right": False},
        ],
        "equalityGroups": [
            [1, [["A", "B"], ["D", "E"]]],
            [2, [["A", "C"], ["D", "F"]]],
        ]
    }


def canvas_i5():
    """I.5: Base angles of isosceles triangle are equal."""
    ax, ay = 325, 100
    bx, by = 150, 400
    cx, cy = 500, 400
    return {
        "points": [
            {"label": "A", "x": ax, "y": ay},
            {"label": "B", "x": bx, "y": by},
            {"label": "C", "x": cx, "y": cy},
        ],
        "segments": [
            {"from": "A", "to": "B", "color": BLUE},
            {"from": "A", "to": "C", "color": BLUE},
            {"from": "B", "to": "C", "color": BLUE},
        ],
        "rays": [],
        "circles": [],
        "angleMarks": [
            {"from": "A", "vertex": "B", "to": "C", "is_right": False},
            {"from": "B", "vertex": "C", "to": "A", "is_right": False},
        ],
        "equalityGroups": [
            [1, [["A", "B"], ["A", "C"]]]
        ]
    }


def canvas_i6():
    """I.6: Converse of I.5 — if base angles equal, triangle is isosceles."""
    ax, ay = 325, 100
    bx, by = 150, 400
    cx, cy = 500, 400
    return {
        "points": [
            {"label": "A", "x": ax, "y": ay},
            {"label": "B", "x": bx, "y": by},
            {"label": "C", "x": cx, "y": cy},
        ],
        "segments": [
            {"from": "A", "to": "B", "color": BLUE},
            {"from": "A", "to": "C", "color": BLUE},
            {"from": "B", "to": "C", "color": BLUE},
        ],
        "rays": [],
        "circles": [],
        "angleMarks": [
            {"from": "A", "vertex": "B", "to": "C", "is_right": False},
            {"from": "B", "vertex": "C", "to": "A", "is_right": False},
        ],
        "equalityGroups": [
            [1, [["A", "B"], ["A", "C"]]]
        ]
    }


def canvas_i7():
    """I.7: Uniqueness of triangle construction on same side of base.
    Given AB with C and D on the same side, if AC=AD and BC=BD then C=D.
    Show the configuration before the contradiction."""
    ax, ay = 150, 380
    bx, by = 450, 380
    # C is a valid triangle vertex
    cx, cy = 300, 150
    # D is a different point (impossible case), shown nearby
    dx, dy = 350, 200
    return {
        "points": [
            {"label": "A", "x": ax, "y": ay},
            {"label": "B", "x": bx, "y": by},
            {"label": "C", "x": cx, "y": cy},
            {"label": "D", "x": dx, "y": dy},
        ],
        "segments": [
            {"from": "A", "to": "B", "color": BLUE},
            {"from": "A", "to": "C", "color": RED},
            {"from": "B", "to": "C", "color": RED},
            {"from": "A", "to": "D", "color": GREEN},
            {"from": "B", "to": "D", "color": GREEN},
        ],
        "rays": [],
        "circles": [],
        "angleMarks": [],
        "equalityGroups": [
            [1, [["A", "C"], ["A", "D"]]],
            [2, [["B", "C"], ["B", "D"]]],
        ]
    }


def canvas_i8():
    """I.8: SSS congruence. Two triangles with three equal sides."""
    ax, ay = 120, 150
    bx, by = 50, 380
    cx, cy = 280, 380
    dx, dy = 420, 150
    ex, ey = 350, 380
    fx, fy = 580, 380
    return {
        "points": [
            {"label": "A", "x": ax, "y": ay},
            {"label": "B", "x": bx, "y": by},
            {"label": "C", "x": cx, "y": cy},
            {"label": "D", "x": dx, "y": dy},
            {"label": "E", "x": ex, "y": ey},
            {"label": "F", "x": fx, "y": fy},
        ],
        "segments": [
            {"from": "A", "to": "B", "color": BLUE},
            {"from": "A", "to": "C", "color": BLUE},
            {"from": "B", "to": "C", "color": BLUE},
            {"from": "D", "to": "E", "color": RED},
            {"from": "D", "to": "F", "color": RED},
            {"from": "E", "to": "F", "color": RED},
        ],
        "rays": [],
        "circles": [],
        "angleMarks": [],
        "equalityGroups": [
            [1, [["A", "B"], ["D", "E"]]],
            [2, [["A", "C"], ["D", "F"]]],
            [3, [["B", "C"], ["E", "F"]]],
        ]
    }


def canvas_i9():
    """I.9: Bisect angle BAC.
    Take D on AB, F on AC at equal distance, construct equilateral triangle
    on DF, then AE bisects the angle."""
    ax, ay = 100, 250
    bx, by = 550, 120
    cx, cy = 550, 380
    # D on AB, F on AC at equal distance from A
    r = 250
    dx, dy = _point_on_line_at_dist(ax, ay, bx, by, r)
    fx, fy = _point_on_line_at_dist(ax, ay, cx, cy, r)
    # E is apex of equilateral triangle on DF (away from A — to the right)
    r_df = _dist(dx, dy, fx, fy)
    # Try both intersections, pick the one farther from A
    e1x, e1y = _circle_intersect(dx, dy, fx, fy, r_df, r_df, top=True)
    e2x, e2y = _circle_intersect(dx, dy, fx, fy, r_df, r_df, top=False)
    if _dist(ax, ay, e1x, e1y) > _dist(ax, ay, e2x, e2y):
        ex, ey = e1x, e1y
    else:
        ex, ey = e2x, e2y
    return {
        "points": [
            {"label": "A", "x": ax, "y": ay},
            {"label": "B", "x": bx, "y": by},
            {"label": "C", "x": cx, "y": cy},
            {"label": "D", "x": round(dx, 2), "y": round(dy, 2)},
            {"label": "F", "x": round(fx, 2), "y": round(fy, 2)},
            {"label": "E", "x": round(ex, 2), "y": round(ey, 2)},
        ],
        "segments": [
            {"from": "A", "to": "B", "color": BLUE},
            {"from": "A", "to": "C", "color": BLUE},
            {"from": "A", "to": "D", "color": GREEN},
            {"from": "A", "to": "F", "color": GREEN},
            {"from": "D", "to": "F", "color": BLACK},
            {"from": "D", "to": "E", "color": RED},
            {"from": "F", "to": "E", "color": RED},
        ],
        "rays": [
            {"from": "A", "through": "E", "color": ORANGE},
        ],
        "circles": [
            {"center": "A", "radius": r, "radius_point": "D", "color": GREEN},
        ],
        "angleMarks": [
            {"from": "B", "vertex": "A", "to": "E", "is_right": False},
            {"from": "E", "vertex": "A", "to": "C", "is_right": False},
        ],
        "equalityGroups": [
            [1, [["A", "D"], ["A", "F"]]],
            [2, [["D", "E"], ["F", "E"]]],
        ]
    }


def canvas_i10():
    """I.10: Bisect segment AB.
    Construct equilateral triangle ABC on AB (I.1),
    then bisect angle ACB (I.9) to find midpoint D."""
    ax, ay = 150, 380
    bx, by = 450, 380
    r = _dist(ax, ay, bx, by)
    # C = apex of equilateral triangle
    cx, cy = _circle_intersect(ax, ay, bx, by, r, r, top=True)
    # D = midpoint of AB (where angle bisector of ACB meets AB)
    dx, dy = _midpoint(ax, ay, bx, by)
    # E = point on angle bisector (between C and D, extended)
    return {
        "points": [
            {"label": "A", "x": ax, "y": ay},
            {"label": "B", "x": bx, "y": by},
            {"label": "C", "x": round(cx, 2), "y": round(cy, 2)},
            {"label": "D", "x": round(dx, 2), "y": round(dy, 2)},
        ],
        "segments": [
            {"from": "A", "to": "B", "color": BLUE},
            {"from": "A", "to": "C", "color": BLACK},
            {"from": "B", "to": "C", "color": BLACK},
            {"from": "C", "to": "D", "color": RED},
        ],
        "rays": [],
        "circles": [
            {"center": "A", "radius": r, "radius_point": "B", "color": GREEN},
            {"center": "B", "radius": r, "radius_point": "A", "color": GREEN},
        ],
        "angleMarks": [
            {"from": "A", "vertex": "C", "to": "D", "is_right": False},
            {"from": "D", "vertex": "C", "to": "B", "is_right": False},
        ],
        "equalityGroups": [
            [1, [["A", "C"], ["B", "C"]]],
            [2, [["A", "D"], ["D", "B"]]],
        ]
    }


def canvas_i11():
    """I.11: Draw perpendicular to line L at point A.
    Constructs point D between A and B, circle at A through D,
    extends to E on other side, builds equilateral triangle DEF off-line,
    then AF is perpendicular to L."""
    # Line L with points A and B
    ax, ay = 200, 350
    bx, by = 500, 350
    # D between A and B (closer to A)
    r_ad = 100
    dx, dy = _point_on_line_at_dist(ax, ay, bx, by, r_ad)
    # E on opposite side of A from D (between(E,A,D)), on circle α centered A radius AD
    ex, ey = _point_on_line_at_dist(ax, ay, bx, by, -r_ad)
    # Equilateral triangle DEF above line L
    r_de = _dist(dx, dy, ex, ey)
    fx, fy = _circle_intersect(dx, dy, ex, ey, r_de, r_de, top=True)
    return {
        "points": [
            {"label": "A", "x": ax, "y": ay},
            {"label": "B", "x": bx, "y": by},
            {"label": "D", "x": round(dx, 2), "y": round(dy, 2)},
            {"label": "E", "x": round(ex, 2), "y": round(ey, 2)},
            {"label": "F", "x": round(fx, 2), "y": round(fy, 2)},
        ],
        "segments": [
            {"from": "A", "to": "B", "color": BLUE},
            {"from": "D", "to": "E", "color": BLACK},
            {"from": "D", "to": "F", "color": RED},
            {"from": "E", "to": "F", "color": RED},
            {"from": "A", "to": "F", "color": GREEN},
        ],
        "rays": [],
        "circles": [
            {"center": "A", "radius": r_ad, "radius_point": "D", "color": BLUE},
            {"center": "D", "radius": r_de, "radius_point": "E", "color": RED},
            {"center": "E", "radius": r_de, "radius_point": "D", "color": RED},
        ],
        "angleMarks": [
            {"from": "B", "vertex": "A", "to": "F", "is_right": True},
        ],
        "equalityGroups": [
            [1, [["A", "D"], ["A", "E"]]],
            [2, [["D", "F"], ["E", "F"]]],
        ]
    }


def canvas_i12():
    """I.12: Drop perpendicular from point P to line L.
    Circle at P through far point D intersects L at E, F.
    Bisect EF at H. PH is perpendicular."""
    # Line L
    ax, ay = 100, 350
    bx, by = 550, 350
    # Point P above line
    px, py = 300, 150
    # D on opposite side of L from P (extend through A past L)
    dx, dy = 300, 500
    # Circle centered P through D
    r_pd = _dist(px, py, dx, dy)
    # Intersections of circle with line L
    ex, ey = _line_circle_intersect(ax, ay, bx, by, px, py, r_pd, far=False)
    fx, fy = _line_circle_intersect(ax, ay, bx, by, px, py, r_pd, far=True)
    # H = midpoint of E and F
    hx, hy = _midpoint(ex, ey, fx, fy)
    return {
        "points": [
            {"label": "A", "x": ax, "y": ay},
            {"label": "B", "x": bx, "y": by},
            {"label": "P", "x": px, "y": py},
            {"label": "D", "x": dx, "y": dy},
            {"label": "E", "x": round(ex, 2), "y": round(ey, 2)},
            {"label": "F", "x": round(fx, 2), "y": round(fy, 2)},
            {"label": "H", "x": round(hx, 2), "y": round(hy, 2)},
        ],
        "segments": [
            {"from": "A", "to": "B", "color": BLUE},
            {"from": "P", "to": "H", "color": GREEN},
            {"from": "P", "to": "E", "color": BLACK},
            {"from": "P", "to": "F", "color": BLACK},
            {"from": "E", "to": "F", "color": BLUE},
        ],
        "rays": [],
        "circles": [
            {"center": "P", "radius": r_pd, "radius_point": "D", "color": RED},
        ],
        "angleMarks": [
            {"from": "E", "vertex": "H", "to": "P", "is_right": True},
        ],
        "equalityGroups": [
            [1, [["P", "E"], ["P", "F"]]],
            [2, [["E", "H"], ["H", "F"]]],
        ]
    }


def canvas_i13():
    """I.13: Supplementary angles on a straight line sum to 2R.
    Line L with between(A,B,C), ray BD off L.
    Angles ABD + DBC = 2 right angles."""
    ax, ay = 100, 350
    cx, cy = 500, 350
    bx, by = 300, 350
    # D above line
    dx, dy = 380, 150
    # Perpendicular E at B (from I.11)
    ex, ey = 300, 150
    return {
        "points": [
            {"label": "A", "x": ax, "y": ay},
            {"label": "B", "x": bx, "y": by},
            {"label": "C", "x": cx, "y": cy},
            {"label": "D", "x": dx, "y": dy},
            {"label": "E", "x": ex, "y": ey},
        ],
        "segments": [
            {"from": "A", "to": "C", "color": BLUE},
            {"from": "B", "to": "D", "color": RED},
            {"from": "B", "to": "E", "color": GREEN},
        ],
        "rays": [],
        "circles": [],
        "angleMarks": [
            {"from": "A", "vertex": "B", "to": "D", "is_right": False},
            {"from": "D", "vertex": "B", "to": "C", "is_right": False},
            {"from": "A", "vertex": "B", "to": "E", "is_right": True},
        ],
        "equalityGroups": []
    }


def canvas_i14():
    """I.14: If angles ABC + ABD = 2R and C,D on opposite sides of L,
    then C-B-D are collinear (between(C,B,D))."""
    ax, ay = 100, 300
    bx, by = 350, 300
    # C above line
    cx, cy = 500, 120
    # D below line (opposite side from C, collinear through B)
    dx, dy = 200, 480
    return {
        "points": [
            {"label": "A", "x": ax, "y": ay},
            {"label": "B", "x": bx, "y": by},
            {"label": "C", "x": cx, "y": cy},
            {"label": "D", "x": dx, "y": dy},
        ],
        "segments": [
            {"from": "A", "to": "B", "color": BLUE},
            {"from": "B", "to": "C", "color": RED},
            {"from": "B", "to": "D", "color": RED},
            {"from": "C", "to": "D", "color": GREEN},
        ],
        "rays": [],
        "circles": [],
        "angleMarks": [
            {"from": "A", "vertex": "B", "to": "C", "is_right": False},
            {"from": "A", "vertex": "B", "to": "D", "is_right": False},
        ],
        "equalityGroups": []
    }


def canvas_i15():
    """I.15: Vertical angles are equal.
    Lines L and M cross at E. between(A,E,B) on L, between(C,E,D) on M.
    Then angle AEC = angle BED."""
    ex, ey = 300, 280
    # Line L: A and B
    ax, ay = 100, 380
    bx, by = 500, 180
    # Line M: C and D
    cx, cy = 130, 130
    dx, dy = 470, 430
    return {
        "points": [
            {"label": "A", "x": ax, "y": ay},
            {"label": "B", "x": bx, "y": by},
            {"label": "C", "x": cx, "y": cy},
            {"label": "D", "x": dx, "y": dy},
            {"label": "E", "x": ex, "y": ey},
        ],
        "segments": [
            {"from": "A", "to": "B", "color": BLUE},
            {"from": "C", "to": "D", "color": RED},
        ],
        "rays": [],
        "circles": [],
        "angleMarks": [
            {"from": "A", "vertex": "E", "to": "C", "is_right": False},
            {"from": "B", "vertex": "E", "to": "D", "is_right": False},
        ],
        "equalityGroups": []
    }


# Map proposition file names to canvas builders
CANVAS_BUILDERS = {
    "Proposition I.1": canvas_i1,
    "Proposition 1.2": canvas_i2,
    "Proposition I.3": canvas_i3,
    "Proposition I.4": canvas_i4,
    "Proposition I.5": canvas_i5,
    "Proposition I.6": canvas_i6,
    "Proposition I.7": canvas_i7,
    "Proposition I.8": canvas_i8,
    "Proposition I.9": canvas_i9,
    "Proposition I.10": canvas_i10,
    "Proposition I.11": canvas_i11,
    "Proposition I.12": canvas_i12,
    "Proposition I.13": canvas_i13,
    "Proposition I.14": canvas_i14,
    "Proposition I.15": canvas_i15,
}


def main():
    for prop_name, builder in CANVAS_BUILDERS.items():
        path = os.path.join(SOLVED_DIR, f"{prop_name}.euclid")
        if not os.path.exists(path):
            print(f"  SKIP {prop_name} — file not found")
            continue

        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)

        canvas = builder()
        data["canvas"] = canvas

        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, ensure_ascii=False)

        n_pts = len(canvas["points"])
        n_seg = len(canvas["segments"])
        n_cir = len(canvas["circles"])
        n_ray = len(canvas["rays"])
        n_ang = len(canvas["angleMarks"])
        n_eq = len(canvas["equalityGroups"])
        print(f"  {prop_name}: {n_pts} pts, {n_seg} seg, {n_cir} cir, "
              f"{n_ray} ray, {n_ang} ang, {n_eq} eq")

    print("\nDone!")


if __name__ == "__main__":
    main()
