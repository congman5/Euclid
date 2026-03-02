import { useState, useRef, useEffect, useCallback, useMemo } from "react";

// ─── DATA: Euclid's Elements Book I ───────────────────────────────────────
const DEFINITIONS = [
  { id: "Def.1", text: "A point is that of which there is no part." },
  { id: "Def.2", text: "A line is a length without breadth." },
  { id: "Def.3", text: "The extremities of a line are points." },
  { id: "Def.4", text: "A straight-line is one which lies evenly with points on itself." },
  { id: "Def.5", text: "A surface is that which has length and breadth only." },
  { id: "Def.6", text: "The extremities of a surface are lines." },
  { id: "Def.7", text: "A plane surface is one which lies evenly with the straight-lines on itself." },
  { id: "Def.8", text: "A plane angle is the inclination of the lines, when two lines in a plane meet one another and are not lying in a straight-line." },
  { id: "Def.9", text: "When the lines containing the angle are straight then the angle is called rectilinear." },
  { id: "Def.10", text: "When a straight-line stood upon another makes adjacent angles equal, each is a right-angle, and the standing line is called perpendicular." },
  { id: "Def.11", text: "An obtuse angle is greater than a right-angle." },
  { id: "Def.12", text: "An acute angle is less than a right-angle." },
  { id: "Def.13", text: "A boundary is that which is the extremity of something." },
  { id: "Def.14", text: "A figure is that which is contained by some boundary or boundaries." },
  { id: "Def.15", text: "A circle is a plane figure contained by a single line such that all straight-lines from one interior point to the circumference are equal." },
  { id: "Def.16", text: "The point is called the center of the circle." },
  { id: "Def.17", text: "A diameter of the circle is any straight-line drawn through the center and terminated by the circumference." },
  { id: "Def.20", text: "An equilateral triangle has three equal sides; isosceles has two equal; scalene has three unequal." },
  { id: "Def.22", text: "A square is right-angled and equilateral; a rectangle right-angled but not equilateral; a rhombus equilateral but not right-angled." },
  { id: "Def.23", text: "Parallel lines are straight-lines in the same plane which, produced to infinity, do not meet." },
];

const POSTULATES = [
  { id: "Post.1", text: "To draw a straight-line from any point to any point." },
  { id: "Post.2", text: "To produce a finite straight-line continuously in a straight-line." },
  { id: "Post.3", text: "To draw a circle with any center and radius." },
  { id: "Post.4", text: "That all right-angles are equal to one another." },
  { id: "Post.5", text: "If a line crossing two lines makes interior angles on one side less than two right-angles, those lines meet on that side." },
];

const COMMON_NOTIONS = [
  { id: "C.N.1", text: "Things equal to the same thing are also equal to one another." },
  { id: "C.N.2", text: "If equal things are added to equal things then the wholes are equal." },
  { id: "C.N.3", text: "If equal things are subtracted from equal things then the remainders are equal." },
  { id: "C.N.4", text: "Things coinciding with one another are equal to one another." },
  { id: "C.N.5", text: "The whole is greater than the part." },
];

const PROOF_FILES = [
  {
    id: "euclid-I.1", source: "euclid", book: "Book I", name: "Proposition I.1",
    title: "Equilateral Triangle Construction",
    statement: "To construct an equilateral triangle on a given finite straight-line.",
    given: "A finite straight-line AB is given.",
    diagramHint: "Draw segment AB. Draw circle centered at A with radius AB, and circle centered at B with radius BA. Mark intersection point C. Join CA and CB.",
    conclusion: "Triangle ABC is equilateral, constructed on the given line AB. Q.E.F.",
    requiredSteps: [
      { keywords: ["circle", "center A", "radius AB"], justification: "Post.3" },
      { keywords: ["circle", "center B", "radius BA"], justification: "Post.3" },
      { keywords: ["join", "CA", "CB"], justification: "Post.1" },
      { keywords: ["AC", "equal", "AB"], justification: "Def.15" },
      { keywords: ["BC", "equal", "BA"], justification: "Def.15" },
      { keywords: ["CA", "CB", "equal"], justification: "C.N.1" },
      { keywords: ["equilateral"], justification: null },
    ]
  },
  {
    id: "euclid-I.2", source: "euclid", book: "Book I", name: "Proposition I.2",
    title: "Transfer a Length to a Point",
    statement: "To place a straight-line equal to a given straight-line at a given point (as an extremity).",
    given: "A point A and a straight-line BC are given.",
    diagramHint: "Join AB. Construct equilateral triangle DAB on AB. Produce DA and DB. Draw circle center B radius BC. Draw circle center D radius DG.",
    conclusion: "The straight-line AL, equal to BC, has been placed at point A. Q.E.F.",
    requiredSteps: [
      { keywords: ["join", "AB"], justification: "Post.1" },
      { keywords: ["equilateral", "triangle", "DAB"], justification: "Prop.I.1" },
      { keywords: ["produce", "DA", "DB"], justification: "Post.2" },
      { keywords: ["circle", "center B", "radius BC"], justification: "Post.3" },
      { keywords: ["circle", "center D", "radius DG"], justification: "Post.3" },
      { keywords: ["BG", "equal", "BC"], justification: "Def.15" },
      { keywords: ["DL", "equal", "DG"], justification: "Def.15" },
      { keywords: ["AL", "equal", "BG"], justification: "C.N.3" },
      { keywords: ["AL", "equal", "BC"], justification: "C.N.1" },
    ]
  },
  {
    id: "euclid-I.3", source: "euclid", book: "Book I", name: "Proposition I.3",
    title: "Cut Off Equal Length",
    statement: "For two given unequal straight-lines, to cut off from the greater a straight-line equal to the lesser.",
    given: "Two unequal straight-lines AB (greater) and C (lesser).",
    diagramHint: "Place line AD equal to C at point A. Draw circle center A radius AD. Mark intersection E on AB.",
    conclusion: "AE, equal to the lesser C, has been cut off from the greater AB. Q.E.F.",
    requiredSteps: [
      { keywords: ["AD", "equal", "C"], justification: "Prop.I.2" },
      { keywords: ["circle", "center A", "radius AD"], justification: "Post.3" },
      { keywords: ["AE", "equal", "AD"], justification: "Def.15" },
      { keywords: ["AE", "equal", "C"], justification: "C.N.1" },
    ]
  },
  {
    id: "euclid-I.4", source: "euclid", book: "Book I", name: "Proposition I.4",
    title: "Side-Angle-Side Congruence (SAS)",
    statement: "If two triangles have two sides equal to two sides respectively, and have the angle enclosed by the equal sides equal, then the base equals the base, the triangle equals the triangle, and the remaining angles are equal.",
    given: "Triangles ABC and DEF with AB=DE, AC=DF, and angle BAC = angle EDF.",
    diagramHint: "Draw two triangles side by side with matching sides and included angle marked.",
    conclusion: "BC=EF, triangle ABC equals triangle DEF, angle ABC=DEF, angle ACB=DFE. Q.E.D.",
    requiredSteps: [
      { keywords: ["apply", "superposition", "triangle ABC", "triangle DEF"], justification: "C.N.4" },
      { keywords: ["B", "coincide", "E"], justification: null },
      { keywords: ["AC", "coincide", "DF"], justification: null },
      { keywords: ["C", "coincide", "F"], justification: null },
      { keywords: ["BC", "coincide", "EF"], justification: "Post.1" },
      { keywords: ["base", "equal"], justification: "C.N.4" },
      { keywords: ["triangle", "equal"], justification: "C.N.4" },
      { keywords: ["remaining", "angles", "equal"], justification: "C.N.4" },
    ]
  },
  {
    id: "euclid-I.5", source: "euclid", book: "Book I", name: "Proposition I.5",
    title: "Isosceles Base Angles (Pons Asinorum)",
    statement: "For isosceles triangles, the angles at the base are equal to one another.",
    given: "Isosceles triangle ABC with AB = AC.",
    diagramHint: "Draw isosceles triangle. Produce AB to D and AC to E. Take point F on BD, cut AG=AF from AE. Join FC and GB.",
    conclusion: "Angle ABC = ACB. Q.E.D.",
    requiredSteps: [
      { keywords: ["F", "random", "BD"], justification: null },
      { keywords: ["AG", "equal", "AF"], justification: "Prop.I.3" },
      { keywords: ["join", "FC", "GB"], justification: "Post.1" },
      { keywords: ["triangle AFC", "equal", "AGB"], justification: "Prop.I.4" },
      { keywords: ["BF", "equal", "CG"], justification: "C.N.3" },
      { keywords: ["triangle BFC", "equal", "CGB"], justification: "Prop.I.4" },
      { keywords: ["ABC", "equal", "ACB"], justification: "C.N.3" },
    ]
  },
  {
    id: "euclid-I.6", source: "euclid", book: "Book I", name: "Proposition I.6",
    title: "Converse of Pons Asinorum",
    statement: "If a triangle has two angles equal then the sides subtending the equal angles are also equal.",
    given: "Triangle ABC with angle ABC = angle ACB.",
    diagramHint: "Draw triangle with equal base angles. Assume AB≠AC for contradiction.",
    conclusion: "AB equals AC. Q.E.D.",
    requiredSteps: [
      { keywords: ["assume", "AB", "unequal", "AC"], justification: null },
      { keywords: ["DB", "equal", "AC"], justification: "Prop.I.3" },
      { keywords: ["triangle DBC", "equal", "ACB"], justification: "Prop.I.4" },
      { keywords: ["lesser", "greater", "absurd"], justification: "C.N.5" },
      { keywords: ["AB", "equal", "AC"], justification: null },
    ]
  },
  {
    id: "euclid-I.8", source: "euclid", book: "Book I", name: "Proposition I.8",
    title: "Side-Side-Side Congruence (SSS)",
    statement: "If two triangles have two sides equal to two sides respectively, and also the base equal, then the angles encompassed by the equal sides are equal.",
    given: "Triangles ABC and DEF with AB=DE, AC=DF, BC=EF.",
    diagramHint: "Draw two triangles with all three pairs of sides marked equal.",
    conclusion: "Angle BAC = angle EDF. Q.E.D.",
    requiredSteps: [
      { keywords: ["apply", "triangle", "BC", "EF"], justification: null },
      { keywords: ["BA", "CA", "coincide", "ED", "DF"], justification: "Prop.I.7" },
      { keywords: ["angle BAC", "equal", "EDF"], justification: "C.N.4" },
    ]
  },
  {
    id: "euclid-I.9", source: "euclid", book: "Book I", name: "Proposition I.9",
    title: "Bisect an Angle",
    statement: "To cut a given rectilinear angle in half.",
    given: "A rectilinear angle BAC.",
    diagramHint: "Take D on AB, cut AE=AD from AC. Construct equilateral triangle DEF. Join AF.",
    conclusion: "Angle BAC has been bisected by line AF. Q.E.F.",
    requiredSteps: [
      { keywords: ["D", "on", "AB"], justification: null },
      { keywords: ["AE", "equal", "AD"], justification: "Prop.I.3" },
      { keywords: ["equilateral", "DEF"], justification: "Prop.I.1" },
      { keywords: ["join", "AF"], justification: "Post.1" },
      { keywords: ["DAF", "equal", "EAF"], justification: "Prop.I.8" },
    ]
  },
  {
    id: "euclid-I.10", source: "euclid", book: "Book I", name: "Proposition I.10",
    title: "Bisect a Segment",
    statement: "To cut a given finite straight-line in half.",
    given: "A finite straight-line AB.",
    diagramHint: "Construct equilateral triangle ABC on AB. Bisect angle ACB with line CD.",
    conclusion: "AB has been bisected at point D. Q.E.F.",
    requiredSteps: [
      { keywords: ["equilateral", "ABC"], justification: "Prop.I.1" },
      { keywords: ["bisect", "ACB", "CD"], justification: "Prop.I.9" },
      { keywords: ["AD", "equal", "BD"], justification: "Prop.I.4" },
    ]
  },
  {
    id: "euclid-I.11", source: "euclid", book: "Book I", name: "Proposition I.11",
    title: "Perpendicular from Point on Line",
    statement: "To draw a straight-line at right-angles to a given straight-line from a given point on it.",
    given: "Straight-line AB and point C on it.",
    diagramHint: "Take D on AC, make CE=CD. Construct equilateral triangle FDE. Join FC.",
    conclusion: "FC is at right angles to AB from point C. Q.E.F.",
    requiredSteps: [
      { keywords: ["CE", "equal", "CD"], justification: "Prop.I.3" },
      { keywords: ["equilateral", "FDE"], justification: "Prop.I.1" },
      { keywords: ["DCF", "equal", "ECF"], justification: "Prop.I.8" },
      { keywords: ["right-angle"], justification: "Def.10" },
    ]
  },
  {
    id: "euclid-I.15", source: "euclid", book: "Book I", name: "Proposition I.15",
    title: "Vertical Angles Are Equal",
    statement: "If two straight-lines cut one another then the vertically opposite angles are equal.",
    given: "Two straight-lines AB and CD cutting at point E.",
    diagramHint: "Draw two crossing lines at E forming four angles.",
    conclusion: "Angle AEC = DEB, and angle CEB = AED. Q.E.D.",
    requiredSteps: [
      { keywords: ["CEA", "AED", "two right-angles"], justification: "Prop.I.13" },
      { keywords: ["AED", "DEB", "two right-angles"], justification: "Prop.I.13" },
      { keywords: ["CEA", "equal", "DEB"], justification: "C.N.3" },
    ]
  },
  {
    id: "euclid-I.16", source: "euclid", book: "Book I", name: "Proposition I.16",
    title: "Exterior Angle Theorem",
    statement: "For any triangle, when one side is produced, the external angle is greater than each internal opposite angle.",
    given: "Triangle ABC with BC produced to D.",
    diagramHint: "Draw triangle, extend BC to D. Bisect AC at E, extend BE to F with EF=BE. Join FC.",
    conclusion: "Angle ACD > angle BAC and angle ACD > angle ABC. Q.E.D.",
    requiredSteps: [
      { keywords: ["bisect", "AC", "E"], justification: "Prop.I.10" },
      { keywords: ["EF", "equal", "BE"], justification: "Prop.I.3" },
      { keywords: ["triangle ABE", "equal", "FEC"], justification: "Prop.I.4" },
      { keywords: ["ACD", "greater", "BAC"], justification: null },
    ]
  },
  {
    id: "euclid-I.29", source: "euclid", book: "Book I", name: "Proposition I.29",
    title: "Parallel Lines Cut by Transversal",
    statement: "A straight-line falling across parallel lines makes alternate angles equal, external angle equal to internal opposite, and co-interior angles supplementary.",
    given: "Parallel lines AB, CD cut by transversal EF at G and H.",
    diagramHint: "Draw two parallel horizontal lines cut by a transversal.",
    conclusion: "AGH=GHD, EGB=GHD, BGH+GHD = two right-angles. Q.E.D.",
    requiredSteps: [
      { keywords: ["assume", "AGH", "unequal", "GHD"], justification: null },
      { keywords: ["BGH", "GHD", "less", "two right-angles"], justification: null },
      { keywords: ["AB", "CD", "meet"], justification: "Post.5" },
      { keywords: ["parallel", "contradiction"], justification: "Def.23" },
      { keywords: ["AGH", "equal", "GHD"], justification: null },
    ]
  },
  {
    id: "euclid-I.32", source: "euclid", book: "Book I", name: "Proposition I.32",
    title: "Angle Sum of a Triangle",
    statement: "The three internal angles of a triangle sum to two right-angles (180°).",
    given: "Triangle ABC with BC produced to D.",
    diagramHint: "Draw triangle, extend BC to D. Draw CE parallel to AB.",
    conclusion: "Angle ABC + BCA + CAB = two right-angles. Q.E.D.",
    requiredSteps: [
      { keywords: ["CE", "parallel", "AB"], justification: "Prop.I.31" },
      { keywords: ["BAC", "equal", "ACE"], justification: "Prop.I.29" },
      { keywords: ["ABC", "equal", "ECD"], justification: "Prop.I.29" },
      { keywords: ["ACD", "equal", "BAC", "ABC"], justification: null },
      { keywords: ["three angles", "two right-angles"], justification: null },
    ]
  },
  {
    id: "euclid-I.47", source: "euclid", book: "Book I", name: "Proposition I.47",
    title: "Pythagorean Theorem",
    statement: "In right-angled triangles, the square on the hypotenuse equals the sum of the squares on the other two sides.",
    given: "Right-angled triangle ABC with right angle BAC.",
    diagramHint: "Draw right triangle with squares on each side. Draw AL parallel to BD through A.",
    conclusion: "The square on BC equals the sum of the squares on BA and AC. Q.E.D.",
    requiredSteps: [
      { keywords: ["square", "on BC"], justification: "Prop.I.46" },
      { keywords: ["square", "on AB"], justification: "Prop.I.46" },
      { keywords: ["square", "on AC"], justification: "Prop.I.46" },
      { keywords: ["AL", "parallel", "BD"], justification: "Prop.I.31" },
      { keywords: ["triangle ABD", "equal", "FBC"], justification: "Prop.I.4" },
      { keywords: ["square BDEC", "equal", "ABFG", "ACKH"], justification: "C.N.2" },
    ]
  },
  {
    id: "euclid-I.48", source: "euclid", book: "Book I", name: "Proposition I.48",
    title: "Converse of Pythagorean Theorem",
    statement: "If BC² = AB² + AC², then angle BAC is a right angle.",
    given: "Triangle ABC where BC² = AB² + AC².",
    diagramHint: "Draw AD perpendicular to AC with AD=AB. Join DC.",
    conclusion: "Angle BAC is a right angle. Q.E.D.",
    requiredSteps: [
      { keywords: ["AD", "perpendicular", "AC"], justification: "Prop.I.11" },
      { keywords: ["AD", "equal", "AB"], justification: "Prop.I.3" },
      { keywords: ["DC²", "equal", "BC²"], justification: "C.N.1" },
      { keywords: ["triangle ABC", "equal", "DAC"], justification: "Prop.I.8" },
      { keywords: ["BAC", "right-angle"], justification: null },
    ]
  },
];

const TEXTBOOK_THEOREMS = [
  {
    id: "tb-thm-2.1", source: "textbook", book: "Ch. 2", name: "Theorem 2.1",
    title: "Unique Midpoint", statement: "Every line segment has exactly one midpoint.",
    given: "A line segment AB.", diagramHint: "Draw segment AB with midpoint M.",
    conclusion: "M is the unique midpoint of AB. Q.E.D.",
    requiredSteps: [
      { keywords: ["midpoint", "AM", "equal", "MB"], justification: "Def. Midpoint" },
      { keywords: ["uniqueness", "contradiction"], justification: null },
    ]
  },
  {
    id: "tb-thm-3.1", source: "textbook", book: "Ch. 3", name: "Theorem 3.1",
    title: "Vertical Angles Theorem", statement: "Vertical angles are congruent.",
    given: "Two lines intersecting at a point.", diagramHint: "Draw two intersecting lines.",
    conclusion: "Each pair of vertical angles is congruent. Q.E.D.",
    requiredSteps: [
      { keywords: ["supplementary", "linear pair"], justification: "Linear Pair Postulate" },
      { keywords: ["vertical angles", "congruent"], justification: "C.N.1" },
    ]
  },
  {
    id: "tb-thm-4.1", source: "textbook", book: "Ch. 4", name: "Theorem 4.1",
    title: "Triangle Angle Sum", statement: "The interior angles of a triangle sum to 180°.",
    given: "Triangle ABC.", diagramHint: "Draw triangle with line through A parallel to BC.",
    conclusion: "m∠A + m∠B + m∠C = 180°. Q.E.D.",
    requiredSteps: [
      { keywords: ["parallel", "through A"], justification: "Parallel Postulate" },
      { keywords: ["alternate interior angles"], justification: "Prop.I.29" },
      { keywords: ["sum", "180"], justification: "Substitution" },
    ]
  },
  {
    id: "tb-thm-5.1", source: "textbook", book: "Ch. 5", name: "Theorem 5.1",
    title: "SAS Congruence", statement: "SAS: Two sides and the included angle congruent implies triangle congruence.",
    given: "△ABC and △DEF with AB≅DE, ∠B≅∠E, BC≅EF.",
    diagramHint: "Draw two triangles with two sides and included angle marked.",
    conclusion: "△ABC ≅ △DEF. Q.E.D.",
    requiredSteps: [
      { keywords: ["AB", "congruent", "DE"], justification: "Given" },
      { keywords: ["angle B", "congruent", "angle E"], justification: "Given" },
      { keywords: ["BC", "congruent", "EF"], justification: "Given" },
      { keywords: ["SAS"], justification: "Prop.I.4" },
    ]
  },
];

const ALL_FILES = [...PROOF_FILES, ...TEXTBOOK_THEOREMS];

// ─── GEOMETRY UTILITIES ───────────────────────────────────────────────────
function dist(a, b) { return Math.sqrt((a.x - b.x) ** 2 + (a.y - b.y) ** 2); }
function lineCircleIntersections(p1, p2, center, radius) {
  const dx = p2.x - p1.x, dy = p2.y - p1.y;
  const fx = p1.x - center.x, fy = p1.y - center.y;
  const a = dx * dx + dy * dy, b = 2 * (fx * dx + fy * dy);
  const c = fx * fx + fy * fy - radius * radius;
  let disc = b * b - 4 * a * c;
  if (disc < 0) return [];
  disc = Math.sqrt(disc);
  const pts = [];
  for (const t of [(-b - disc) / (2 * a), (-b + disc) / (2 * a)]) {
    if (t >= -0.01 && t <= 1.01) pts.push({ x: p1.x + t * dx, y: p1.y + t * dy });
  }
  return pts;
}
function circleCircleIntersections(c1, r1, c2, r2) {
  const d = dist(c1, c2);
  if (d > r1 + r2 + 1 || d < Math.abs(r1 - r2) - 1 || d < 0.1) return [];
  const a = (r1 * r1 - r2 * r2 + d * d) / (2 * d);
  const h2 = r1 * r1 - a * a;
  if (h2 < 0) return [];
  const h = Math.sqrt(h2);
  const px = c1.x + a * (c2.x - c1.x) / d, py = c1.y + a * (c2.y - c1.y) / d;
  return [
    { x: px + h * (c2.y - c1.y) / d, y: py - h * (c2.x - c1.x) / d },
    { x: px - h * (c2.y - c1.y) / d, y: py + h * (c2.x - c1.x) / d },
  ];
}
function segSegIntersection(a1, a2, b1, b2) {
  const d1x = a2.x - a1.x, d1y = a2.y - a1.y, d2x = b2.x - b1.x, d2y = b2.y - b1.y;
  const cross = d1x * d2y - d1y * d2x;
  if (Math.abs(cross) < 0.001) return null;
  const t = ((b1.x - a1.x) * d2y - (b1.y - a1.y) * d2x) / cross;
  const u = ((b1.x - a1.x) * d1y - (b1.y - a1.y) * d1x) / cross;
  if (t >= -0.01 && t <= 1.01 && u >= -0.01 && u <= 1.01)
    return { x: a1.x + t * d1x, y: a1.y + t * d1y };
  return null;
}

const SNAP_DIST = 14;
const COLORS = {
  parchment: "#f5ecd7", parchmentDark: "#e8d9b5", ink: "#2c1810", inkLight: "#5a3825",
  gold: "#c9a84c", goldBright: "#dabb5c", goldDim: "#a08030", red: "#8b2500",
  blue: "#1a3a5c", green: "#2d5a27", snapHighlight: "#d4af37",
  gridLine: "rgba(44,24,16,0.06)", canvasBg: "#faf3e3",
};
const LINE_COLORS = [
  { id: "ink", label: "Ink", hex: "#2c1810" },
  { id: "blue", label: "Blue", hex: "#1a5a8c" },
  { id: "red", label: "Red", hex: "#8b2500" },
  { id: "green", label: "Green", hex: "#2d6a27" },
  { id: "purple", label: "Purple", hex: "#5c2a7c" },
  { id: "orange", label: "Orange", hex: "#b86514" },
  { id: "teal", label: "Teal", hex: "#1a7a6a" },
];

// ─── RESIZABLE PANEL HOOK ─────────────────────────────────────────────────
function useResizable(initialWidth, minW, maxW, side = "left") {
  const [width, setWidth] = useState(initialWidth);
  const dragging = useRef(false);
  const startX = useRef(0);
  const startW = useRef(0);

  const onMouseDown = useCallback((e) => {
    e.preventDefault();
    dragging.current = true;
    startX.current = e.clientX;
    startW.current = width;
    const onMove = (ev) => {
      if (!dragging.current) return;
      const delta = side === "left" ? (startX.current - ev.clientX) : (ev.clientX - startX.current);
      setWidth(Math.max(minW, Math.min(maxW, startW.current + delta)));
    };
    const onUp = () => { dragging.current = false; window.removeEventListener("mousemove", onMove); window.removeEventListener("mouseup", onUp); };
    window.addEventListener("mousemove", onMove);
    window.addEventListener("mouseup", onUp);
  }, [width, minW, maxW, side]);

  return { width, onMouseDown };
}

// ─── MAIN COMPONENT ──────────────────────────────────────────────────────
export default function EuclidSimulator() {
  const [screen, setScreen] = useState("home");
  const [currentFile, setCurrentFile] = useState(null);
  const [searchTerm, setSearchTerm] = useState("");
  const [filterSource, setFilterSource] = useState("all");

  // Canvas state
  const [points, setPoints] = useState([]);
  const [segments, setSegments] = useState([]);
  const [circles, setCircles] = useState([]);
  const [angleMarks, setAngleMarks] = useState([]);
  const [tool, setTool] = useState("point");
  const [activeColor, setActiveColor] = useState("#2c1810");
  const [pendingClick, setPendingClick] = useState(null);
  const [nextLabel, setNextLabel] = useState(0);
  const [snapTarget, setSnapTarget] = useState(null);
  const [mousePos, setMousePos] = useState({ x: 0, y: 0 });
  const [canvasSize, setCanvasSize] = useState({ w: 800, h: 600 });

  // Journal
  const [journalSteps, setJournalSteps] = useState([]);
  const [conclusionText, setConclusionText] = useState("");
  const [verificationResult, setVerificationResult] = useState(null);
  const [showReference, setShowReference] = useState(false);
  const [refTab, setRefTab] = useState("postulates");
  const [showPropositions, setShowPropositions] = useState(false);

  const canvasRef = useRef(null);
  const canvasWrapRef = useRef(null);
  const LABEL = (i) => String.fromCharCode(65 + (i % 26)) + (i >= 26 ? String(Math.floor(i / 26)) : "");

  // Resizable panels
  const journalPanel = useResizable(330, 200, 550, "left");
  const refPanel = useResizable(280, 180, 450, "left");

  // ── Canvas resize observer — match internal resolution to display size ──
  useEffect(() => {
    const wrap = canvasWrapRef.current;
    if (!wrap) return;
    const ro = new ResizeObserver((entries) => {
      for (const entry of entries) {
        const { width, height } = entry.contentRect;
        if (width > 0 && height > 0) {
          setCanvasSize({ w: Math.round(width), h: Math.round(height) });
        }
      }
    });
    ro.observe(wrap);
    return () => ro.disconnect();
  }, [screen]);

  // Sync canvas element dimensions to state
  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    canvas.width = canvasSize.w;
    canvas.height = canvasSize.h;
  }, [canvasSize]);

  // ── Storage ──
  const saveState = useCallback(async () => {
    if (!currentFile) return;
    const state = { points, segments, circles, angleMarks, journalSteps, conclusionText, nextLabel };
    try { await window.storage?.set(`proof:${currentFile.id}`, JSON.stringify(state)); } catch (e) { /* ok */ }
  }, [currentFile, points, segments, circles, angleMarks, journalSteps, conclusionText, nextLabel]);

  const loadState = useCallback(async (file) => {
    try {
      const result = await window.storage?.get(`proof:${file.id}`);
      if (result?.value) {
        const s = JSON.parse(result.value);
        setPoints(s.points || []); setSegments(s.segments || []);
        setCircles(s.circles || []); setAngleMarks(s.angleMarks || []);
        setJournalSteps(s.journalSteps || []); setConclusionText(s.conclusionText || "");
        setNextLabel(s.nextLabel || 0); return;
      }
    } catch (e) { /* ok */ }
    setPoints([]); setSegments([]); setCircles([]); setAngleMarks([]);
    setJournalSteps([]); setConclusionText(file?.conclusion || ""); setNextLabel(0);
  }, []);

  // ── Auto-journal helper ──
  const autoLog = useCallback((text, justification = "Construction") => {
    setJournalSteps(prev => [...prev, { text, justification }]);
  }, []);

  // ── Snap points computation ──
  const allSnapPoints = useMemo(() => {
    const snaps = points.map(p => ({ ...p, type: "point" }));
    for (let i = 0; i < segments.length; i++) {
      for (let j = i + 1; j < segments.length; j++) {
        const si = segments[i], sj = segments[j];
        const pi1 = points.find(p => p.label === si.from), pi2 = points.find(p => p.label === si.to);
        const pj1 = points.find(p => p.label === sj.from), pj2 = points.find(p => p.label === sj.to);
        if (pi1 && pi2 && pj1 && pj2) {
          const ix = segSegIntersection(pi1, pi2, pj1, pj2);
          if (ix && !snaps.some(s => dist(s, ix) < 4)) snaps.push({ ...ix, type: "intersection", label: "×" });
        }
      }
    }
    circles.forEach(c => {
      const cp = points.find(p => p.label === c.center);
      if (cp && !snaps.some(s => s.label === cp.label)) snaps.push({ ...cp, type: "center" });
    });
    for (let i = 0; i < circles.length; i++) {
      for (let j = i + 1; j < circles.length; j++) {
        const c1p = points.find(p => p.label === circles[i].center);
        const c2p = points.find(p => p.label === circles[j].center);
        if (c1p && c2p) {
          circleCircleIntersections(c1p, circles[i].radius, c2p, circles[j].radius).forEach(ix => {
            if (!snaps.some(s => dist(s, ix) < 4)) snaps.push({ ...ix, type: "intersection", label: "×" });
          });
        }
      }
    }
    for (const seg of segments) {
      const p1 = points.find(p => p.label === seg.from), p2 = points.find(p => p.label === seg.to);
      if (!p1 || !p2) continue;
      for (const circ of circles) {
        const cp = points.find(p => p.label === circ.center);
        if (!cp) continue;
        lineCircleIntersections(p1, p2, cp, circ.radius).forEach(ix => {
          if (!snaps.some(s => dist(s, ix) < 4)) snaps.push({ ...ix, type: "intersection", label: "×" });
        });
      }
    }
    return snaps;
  }, [points, segments, circles]);

  const findSnap = useCallback((mx, my) => {
    let closest = null, minD = SNAP_DIST;
    for (const s of allSnapPoints) {
      const d = dist({ x: mx, y: my }, s);
      if (d < minD) { minD = d; closest = s; }
    }
    return closest;
  }, [allSnapPoints]);

  // ── CORRECT coordinate transform: CSS pixels → canvas pixels ──
  const getCanvasPos = useCallback((e) => {
    const canvas = canvasRef.current;
    if (!canvas) return { x: 0, y: 0 };
    const rect = canvas.getBoundingClientRect();
    // Map from display (CSS) coords to internal canvas coords
    const scaleX = canvas.width / rect.width;
    const scaleY = canvas.height / rect.height;
    return {
      x: (e.clientX - rect.left) * scaleX,
      y: (e.clientY - rect.top) * scaleY,
    };
  }, []);

  const handleCanvasMove = useCallback((e) => {
    const pos = getCanvasPos(e);
    setMousePos(pos);
    setSnapTarget(findSnap(pos.x, pos.y));
  }, [getCanvasPos, findSnap]);

  // Get or create a point at position, return label
  const ensurePoint = useCallback((x, y, snap) => {
    if (snap?.type === "point") return snap.label;
    // Check if near existing point
    const existing = points.find(p => dist(p, { x, y }) < 5);
    if (existing) return existing.label;
    const label = LABEL(nextLabel);
    setPoints(prev => [...prev, { x, y, label }]);
    setNextLabel(prev => prev + 1);
    return label;
  }, [points, nextLabel]);

  const handleCanvasClick = useCallback((e) => {
    const raw = getCanvasPos(e);
    const snap = findSnap(raw.x, raw.y);
    const pos = snap && (snap.type === "point" || snap.type === "intersection" || snap.type === "center") ? snap : raw;
    const x = pos.x, y = pos.y;

    if (tool === "point") {
      if (snap?.type === "point") return; // already exists
      const label = LABEL(nextLabel);
      setPoints(prev => [...prev, { x, y, label }]);
      setNextLabel(prev => prev + 1);
      autoLog(`Placed point ${label} at (${Math.round(x)}, ${Math.round(y)})`, "Construction");
    } else if (tool === "segment" || tool === "ray") {
      if (!pendingClick) {
        const label = ensurePoint(x, y, snap);
        setPendingClick(label);
      } else {
        const label = ensurePoint(x, y, snap);
        if (label !== pendingClick) {
          const type = tool === "ray" ? "ray" : "segment";
          setSegments(prev => [...prev, { from: pendingClick, to: label, isRay: tool === "ray", color: activeColor }]);
          autoLog(
            type === "ray"
              ? `Drew ray from ${pendingClick} through ${label}`
              : `Drew segment ${pendingClick}${label}`,
            "Post.1"
          );
        }
        setPendingClick(null);
      }
    } else if (tool === "circle") {
      if (!pendingClick) {
        const label = ensurePoint(x, y, snap);
        setPendingClick(label);
      } else {
        const center = points.find(p => p.label === pendingClick);
        if (!center) { setPendingClick(null); return; }
        const radius = dist(center, { x, y });
        if (radius > 5) {
          // Find what the radius endpoint is, for labeling
          const edgePt = snap?.type === "point" ? snap.label : null;
          setCircles(prev => [...prev, { center: pendingClick, radius, color: activeColor }]);
          autoLog(
            `Drew circle with center ${pendingClick}${edgePt ? ` and radius ${pendingClick}${edgePt}` : ` (r≈${Math.round(radius)})`}`,
            "Post.3"
          );
        }
        setPendingClick(null);
      }
    } else if (tool === "angle") {
      if (!pendingClick) {
        setPendingClick({ pts: [ensurePoint(x, y, snap)] });
      } else if (pendingClick.pts?.length === 1) {
        setPendingClick({ pts: [...pendingClick.pts, ensurePoint(x, y, snap)] });
      } else if (pendingClick.pts?.length === 2) {
        const third = ensurePoint(x, y, snap);
        const [from, vertex] = pendingClick.pts;
        setAngleMarks(prev => [...prev, { from, vertex, to: third, color: activeColor }]);
        autoLog(`Marked angle ∠${from}${vertex}${third}`, "Construction");
        setPendingClick(null);
      }
    } else if (tool === "measure") {
      if (!pendingClick) {
        if (snap?.type === "point") setPendingClick(snap.label);
      } else {
        if (snap?.type === "point" && snap.label !== pendingClick) {
          const p1 = points.find(p => p.label === pendingClick);
          const p2 = points.find(p => p.label === snap.label);
          if (p1 && p2) {
            const d = dist(p1, p2);
            autoLog(`Measured ${pendingClick}${snap.label} = ${d.toFixed(1)} units`, "Construction");
          }
        }
        setPendingClick(null);
      }
    }
  }, [tool, pendingClick, activeColor, points, nextLabel, getCanvasPos, findSnap, ensurePoint, autoLog]);

  // ── Canvas draw ──
  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    const ctx = canvas.getContext("2d");
    const W = canvas.width, H = canvas.height;

    ctx.clearRect(0, 0, W, H);
    ctx.fillStyle = COLORS.canvasBg;
    ctx.fillRect(0, 0, W, H);

    // Grid
    ctx.strokeStyle = COLORS.gridLine;
    ctx.lineWidth = 0.5;
    for (let gx = 0; gx < W; gx += 40) { ctx.beginPath(); ctx.moveTo(gx, 0); ctx.lineTo(gx, H); ctx.stroke(); }
    for (let gy = 0; gy < H; gy += 40) { ctx.beginPath(); ctx.moveTo(0, gy); ctx.lineTo(W, gy); ctx.stroke(); }

    // Circles
    circles.forEach(c => {
      const cp = points.find(p => p.label === c.center);
      if (!cp) return;
      ctx.beginPath();
      ctx.arc(cp.x, cp.y, c.radius, 0, Math.PI * 2);
      ctx.strokeStyle = c.color || COLORS.blue;
      ctx.lineWidth = 1.8;
      ctx.stroke();
      ctx.beginPath();
      ctx.arc(cp.x, cp.y, 2.5, 0, Math.PI * 2);
      ctx.fillStyle = c.color || COLORS.blue;
      ctx.fill();
    });

    // Segments
    segments.forEach(s => {
      const p1 = points.find(p => p.label === s.from), p2 = points.find(p => p.label === s.to);
      if (!p1 || !p2) return;
      ctx.beginPath();
      if (s.isRay) {
        const dx = p2.x - p1.x, dy = p2.y - p1.y;
        const len = Math.sqrt(dx * dx + dy * dy) || 1;
        ctx.moveTo(p1.x, p1.y);
        ctx.lineTo(p1.x + (dx / len) * 3000, p1.y + (dy / len) * 3000);
      } else {
        ctx.moveTo(p1.x, p1.y);
        ctx.lineTo(p2.x, p2.y);
      }
      ctx.strokeStyle = s.color || COLORS.ink;
      ctx.lineWidth = 2;
      ctx.stroke();
    });

    // Angle arcs
    angleMarks.forEach(a => {
      const pf = points.find(p => p.label === a.from);
      const pv = points.find(p => p.label === a.vertex);
      const pt = points.find(p => p.label === a.to);
      if (!pf || !pv || !pt) return;
      let ang1 = Math.atan2(pf.y - pv.y, pf.x - pv.x);
      let ang2 = Math.atan2(pt.y - pv.y, pt.x - pv.x);
      // Always draw the smaller arc
      let diff = ang2 - ang1;
      if (diff > Math.PI) ang2 -= 2 * Math.PI;
      if (diff < -Math.PI) ang2 += 2 * Math.PI;
      ctx.beginPath();
      ctx.arc(pv.x, pv.y, 24, Math.min(ang1, ang2), Math.max(ang1, ang2));
      ctx.strokeStyle = a.color || COLORS.red;
      ctx.lineWidth = 2;
      ctx.stroke();
    });

    // Points
    points.forEach(p => {
      ctx.beginPath();
      ctx.arc(p.x, p.y, 4.5, 0, Math.PI * 2);
      ctx.fillStyle = COLORS.ink;
      ctx.fill();
      ctx.beginPath();
      ctx.arc(p.x, p.y, 2, 0, Math.PI * 2);
      ctx.fillStyle = COLORS.canvasBg;
      ctx.fill();
      ctx.font = `bold ${Math.max(13, Math.min(16, W / 60))}px 'Georgia', serif`;
      ctx.fillStyle = COLORS.ink;
      ctx.fillText(p.label, p.x + 8, p.y - 8);
    });

    // Snap crosshair
    if (snapTarget) {
      ctx.save();
      const sx = snapTarget.x, sy = snapTarget.y;
      ctx.strokeStyle = COLORS.snapHighlight;
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.moveTo(sx - 12, sy); ctx.lineTo(sx + 12, sy);
      ctx.moveTo(sx, sy - 12); ctx.lineTo(sx, sy + 12);
      ctx.stroke();
      ctx.beginPath();
      ctx.arc(sx, sy, 9, 0, Math.PI * 2);
      ctx.strokeStyle = COLORS.snapHighlight + "88";
      ctx.lineWidth = 2;
      ctx.stroke();
      // Label
      if (snapTarget.type !== "point") {
        ctx.fillStyle = COLORS.snapHighlight;
        ctx.font = "11px Georgia, serif";
        ctx.fillText(snapTarget.type, sx + 12, sy + 16);
      }
      ctx.restore();
    }

    // Preview
    if (pendingClick) {
      const fromLabel = typeof pendingClick === "string" ? pendingClick : pendingClick.pts?.[pendingClick.pts.length - 1];
      const from = fromLabel ? points.find(p => p.label === fromLabel) : null;
      if (from) {
        ctx.save();
        ctx.setLineDash([5, 5]);
        ctx.lineWidth = 1.5;
        if (tool === "circle") {
          const r = dist(from, mousePos);
          ctx.beginPath();
          ctx.arc(from.x, from.y, r, 0, Math.PI * 2);
          ctx.strokeStyle = (activeColor || COLORS.blue) + "66";
          ctx.stroke();
        } else {
          ctx.beginPath();
          ctx.moveTo(from.x, from.y);
          ctx.lineTo(mousePos.x, mousePos.y);
          ctx.strokeStyle = (activeColor || COLORS.ink) + "88";
          ctx.stroke();
        }
        ctx.setLineDash([]);
        ctx.restore();
      }
    }
  }, [points, segments, circles, angleMarks, snapTarget, pendingClick, tool, mousePos, canvasSize, activeColor]);

  // ── Journal ──
  const addJournalStep = () => setJournalSteps(prev => [...prev, { text: "", justification: "" }]);
  const updateStep = (idx, field, value) => setJournalSteps(prev => prev.map((s, i) => i === idx ? { ...s, [field]: value } : s));
  const removeStep = (idx) => setJournalSteps(prev => prev.filter((_, i) => i !== idx));
  const moveStep = (idx, dir) => {
    setJournalSteps(prev => {
      const arr = [...prev];
      const newIdx = idx + dir;
      if (newIdx < 0 || newIdx >= arr.length) return arr;
      [arr[idx], arr[newIdx]] = [arr[newIdx], arr[idx]];
      return arr;
    });
  };

  // ── Verify ──
  const verifyProof = () => {
    if (!currentFile?.requiredSteps) {
      setVerificationResult({ type: "info", message: "Freeform proof — no answer key to verify against." });
      return;
    }
    const fullText = journalSteps.map(s => `${s.text} ${s.justification}`).join("\n").toLowerCase();
    const results = currentFile.requiredSteps.map((req, i) => {
      const kw = req.keywords.every(k => fullText.includes(k.toLowerCase()));
      const jst = !req.justification || fullText.includes(req.justification.toLowerCase());
      return { step: i + 1, keywords: req.keywords, required: req.justification, satisfied: kw && jst, keywordMatch: kw, justMatch: jst };
    });
    setVerificationResult({ type: results.every(r => r.satisfied) ? "success" : "partial", results, allSatisfied: results.every(r => r.satisfied) });
  };

  // ── Apply proposition ──
  const applyProposition = (propId) => {
    const prop = ALL_FILES.find(f => f.id === propId);
    if (!prop) return;
    autoLog(`Applied ${prop.name}: ${prop.title}`, prop.name.replace("Proposition ", "Prop."));
    // Auto-construct equilateral triangle for I.1
    if (propId === "euclid-I.1" && segments.length > 0) {
      const seg = segments[segments.length - 1];
      const p1 = points.find(p => p.label === seg.from), p2 = points.find(p => p.label === seg.to);
      if (p1 && p2) {
        const r = dist(p1, p2);
        setCircles(prev => [...prev, { center: seg.from, radius: r, color: COLORS.blue }, { center: seg.to, radius: r, color: COLORS.blue }]);
        const ints = circleCircleIntersections(p1, r, p2, r);
        if (ints.length > 0) {
          const top = ints.reduce((a, b) => a.y < b.y ? a : b);
          const label = LABEL(nextLabel);
          setPoints(prev => [...prev, { x: top.x, y: top.y, label }]);
          setSegments(prev => [...prev, { from: label, to: seg.from, color: activeColor }, { from: label, to: seg.to, color: activeColor }]);
          setNextLabel(prev => prev + 1);
        }
      }
    }
  };

  const openFile = (file) => {
    setCurrentFile(file);
    loadState(file);
    setVerificationResult(null);
    setShowReference(false);
    setShowPropositions(false);
    setScreen("proof");
  };
  const openBlankFile = () => openFile({
    id: `blank-${Date.now()}`, source: "custom", book: "Custom", name: "New Proof",
    title: "Freeform Proof", statement: "Write your own proposition here.",
    given: "", diagramHint: "", conclusion: "", requiredSteps: null,
  });
  const clearCanvas = () => { setPoints([]); setSegments([]); setCircles([]); setAngleMarks([]); setNextLabel(0); setPendingClick(null); };

  // ═══════════════════ HOME SCREEN ═══════════════════════════════════════
  if (screen === "home") {
    const filtered = ALL_FILES.filter(f => {
      if (filterSource !== "all" && f.source !== filterSource) return false;
      if (searchTerm && !`${f.name} ${f.title} ${f.statement}`.toLowerCase().includes(searchTerm.toLowerCase())) return false;
      return true;
    });
    const grouped = {};
    filtered.forEach(f => {
      const key = `${f.source === "euclid" ? "Euclid's Elements" : "Textbook"} — ${f.book}`;
      (grouped[key] ||= []).push(f);
    });

    return (
      <div style={{ minHeight: "100vh", background: `linear-gradient(135deg, ${COLORS.ink} 0%, #1a0f08 100%)`, fontFamily: "'Georgia', 'Crimson Text', serif", color: COLORS.parchment }}>
        <div style={{ textAlign: "center", padding: "48px 20px 12px" }}>
          <div style={{ fontSize: 11, letterSpacing: 8, color: COLORS.goldDim, textTransform: "uppercase", marginBottom: 8 }}>Στοιχεῖα</div>
          <h1 style={{ fontSize: 44, fontWeight: 400, color: COLORS.gold, margin: 0, letterSpacing: 3 }}>ELEMENTS</h1>
          <div style={{ fontSize: 15, color: COLORS.parchmentDark, marginTop: 6, fontStyle: "italic" }}>Interactive Geometric Proof Simulator</div>
          <div style={{ width: 120, height: 1, background: `linear-gradient(90deg, transparent, ${COLORS.gold}, transparent)`, margin: "18px auto" }} />
        </div>
        <div style={{ maxWidth: 740, margin: "0 auto", padding: "0 20px 60px" }}>
          <div style={{ display: "flex", gap: 10, marginBottom: 16, flexWrap: "wrap" }}>
            <input value={searchTerm} onChange={e => setSearchTerm(e.target.value)} placeholder="Search propositions..."
              style={{ flex: 1, minWidth: 200, padding: "10px 16px", background: "rgba(245,236,215,0.08)", border: `1px solid ${COLORS.goldDim}44`, borderRadius: 6, color: COLORS.parchment, fontFamily: "inherit", fontSize: 14, outline: "none" }} />
            <div style={{ display: "flex", gap: 4 }}>
              {[["all", "All"], ["euclid", "Euclid"], ["textbook", "Textbook"]].map(([v, l]) => (
                <button key={v} onClick={() => setFilterSource(v)}
                  style={{ padding: "8px 16px", background: filterSource === v ? COLORS.gold : "transparent", color: filterSource === v ? COLORS.ink : COLORS.parchmentDark, border: `1px solid ${COLORS.goldDim}66`, borderRadius: 4, cursor: "pointer", fontFamily: "inherit", fontSize: 13, fontWeight: filterSource === v ? 700 : 400 }}>{l}</button>
              ))}
            </div>
          </div>
          <button onClick={openBlankFile} style={{ width: "100%", padding: "14px", marginBottom: 24, background: "rgba(201,168,76,0.1)", border: `1px dashed ${COLORS.goldDim}`, borderRadius: 8, color: COLORS.gold, cursor: "pointer", fontFamily: "inherit", fontSize: 15, letterSpacing: 1 }}>✦ Create Blank Proof File</button>
          {Object.entries(grouped).map(([group, files]) => (
            <div key={group} style={{ marginBottom: 28 }}>
              <h3 style={{ fontSize: 12, textTransform: "uppercase", letterSpacing: 3, color: COLORS.goldDim, marginBottom: 8, borderBottom: `1px solid ${COLORS.goldDim}33`, paddingBottom: 6 }}>{group}</h3>
              {files.map(f => (
                <button key={f.id} onClick={() => openFile(f)}
                  style={{ display: "block", width: "100%", textAlign: "left", padding: "12px 16px", marginBottom: 6, background: "rgba(245,236,215,0.04)", border: `1px solid ${COLORS.goldDim}22`, borderRadius: 6, cursor: "pointer", transition: "all 0.15s", fontFamily: "inherit" }}
                  onMouseEnter={e => { e.currentTarget.style.background = "rgba(201,168,76,0.12)"; e.currentTarget.style.borderColor = COLORS.goldDim + "66"; }}
                  onMouseLeave={e => { e.currentTarget.style.background = "rgba(245,236,215,0.04)"; e.currentTarget.style.borderColor = COLORS.goldDim + "22"; }}>
                  <div style={{ display: "flex", justifyContent: "space-between", alignItems: "baseline" }}>
                    <span style={{ color: COLORS.gold, fontWeight: 600, fontSize: 15 }}>{f.name}</span>
                    <span style={{ fontSize: 12, color: COLORS.parchmentDark }}>{f.source === "euclid" ? "📜" : "📖"}</span>
                  </div>
                  <div style={{ color: COLORS.parchmentDark, fontSize: 13, marginTop: 2 }}>{f.title}</div>
                  <div style={{ color: COLORS.parchmentDark + "99", fontSize: 12, marginTop: 4, lineHeight: 1.4 }}>{f.statement.slice(0, 130)}{f.statement.length > 130 ? "…" : ""}</div>
                </button>
              ))}
            </div>
          ))}
          <div style={{ textAlign: "center", padding: "20px 0", color: COLORS.parchmentDark + "55", fontSize: 12 }}>Architecture inspired by Aris (Bram-Hub) · BRAM file-based proof workflow</div>
        </div>
      </div>
    );
  }

  // ═══════════════════ PROOF WORKSPACE ════════════════════════════════════
  const DragHandle = ({ onMouseDown: onMD, side }) => (
    <div onMouseDown={onMD} style={{ width: 5, cursor: "col-resize", background: `linear-gradient(180deg, transparent 20%, ${COLORS.goldDim}33 50%, transparent 80%)`, flexShrink: 0, position: "relative", zIndex: 2 }}
      onMouseEnter={e => e.currentTarget.style.background = COLORS.goldDim + "66"}
      onMouseLeave={e => e.currentTarget.style.background = `linear-gradient(180deg, transparent 20%, ${COLORS.goldDim}33 50%, transparent 80%)`} />
  );

  const toolButtons = [
    { id: "point", label: "Point", icon: "•" },
    { id: "segment", label: "Line", icon: "—" },
    { id: "ray", label: "Ray", icon: "→" },
    { id: "circle", label: "Circle", icon: "○" },
    { id: "angle", label: "Angle", icon: "∠" },
    { id: "measure", label: "Ruler", icon: "📏" },
  ];

  const statusText = pendingClick
    ? tool === "angle" && pendingClick.pts
      ? `Click ${3 - pendingClick.pts.length} more point${pendingClick.pts.length < 2 ? "s" : ""} (from → vertex → to)`
      : "Click second point…"
    : null;

  return (
    <div style={{ display: "flex", flexDirection: "column", height: "100vh", fontFamily: "'Georgia', 'Crimson Text', serif", background: COLORS.ink, color: COLORS.parchment, overflow: "hidden" }}>
      {/* ── Top Bar ── */}
      <div style={{ display: "flex", alignItems: "center", justifyContent: "space-between", padding: "6px 12px", background: "#1a0f08", borderBottom: `1px solid ${COLORS.goldDim}33`, flexShrink: 0, minHeight: 40, gap: 8 }}>
        <div style={{ display: "flex", alignItems: "center", gap: 10, minWidth: 0 }}>
          <button onClick={() => { saveState(); setScreen("home"); }} style={{ background: "none", border: "none", color: COLORS.gold, cursor: "pointer", fontSize: 18, padding: "2px 6px" }}>◂</button>
          <span style={{ color: COLORS.gold, fontWeight: 600, fontSize: 15, whiteSpace: "nowrap" }}>{currentFile?.name}</span>
          <span style={{ color: COLORS.parchmentDark, fontSize: 13, overflow: "hidden", textOverflow: "ellipsis", whiteSpace: "nowrap" }}>— {currentFile?.title}</span>
        </div>
        <div style={{ display: "flex", gap: 6, alignItems: "center", flexShrink: 0 }}>
          <button onClick={saveState} style={{ ...btnStyle(), background: "rgba(201,168,76,0.15)" }}>Save</button>
          <button onClick={() => setShowPropositions(p => !p)} style={{ ...btnStyle(), background: showPropositions ? COLORS.gold : "rgba(201,168,76,0.15)", color: showPropositions ? COLORS.ink : COLORS.gold }}>Propositions</button>
          <button onClick={() => setShowReference(r => !r)} style={{ ...btnStyle(), background: showReference ? COLORS.gold : "rgba(201,168,76,0.15)", color: showReference ? COLORS.ink : COLORS.gold }}>Reference</button>
        </div>
      </div>

      {/* ── Proposition Statement ── */}
      <div style={{ padding: "8px 14px", background: "rgba(201,168,76,0.06)", borderBottom: `1px solid ${COLORS.goldDim}22`, fontSize: 13, lineHeight: 1.5, flexShrink: 0 }}>
        <strong style={{ color: COLORS.gold }}>Proposition: </strong><span>{currentFile?.statement}</span>
        {currentFile?.given && <><br /><strong style={{ color: COLORS.goldDim }}>Given: </strong><span style={{ color: COLORS.parchmentDark }}>{currentFile.given}</span></>}
      </div>

      {/* ── Main Layout ── */}
      <div style={{ display: "flex", flex: 1, overflow: "hidden" }}>

        {/* Left sidebars (Propositions / Reference) */}
        {showPropositions && (<>
          <div style={{ width: refPanel.width, display: "flex", flexDirection: "column", background: "rgba(0,0,0,0.3)", overflow: "hidden", flexShrink: 0 }}>
            <div style={{ padding: "8px 10px", borderBottom: `1px solid ${COLORS.goldDim}22` }}>
              <h4 style={{ margin: 0, fontSize: 11, color: COLORS.gold, letterSpacing: 2, textTransform: "uppercase" }}>Apply Construction</h4>
            </div>
            <div style={{ flex: 1, overflow: "auto", padding: 8 }}>
              {ALL_FILES.filter(f => f.requiredSteps).map(f => (
                <button key={f.id} onClick={() => applyProposition(f.id)}
                  style={{ display: "block", width: "100%", textAlign: "left", padding: "7px 9px", marginBottom: 4, background: "rgba(245,236,215,0.04)", border: `1px solid ${COLORS.goldDim}22`, borderRadius: 4, cursor: "pointer", color: COLORS.parchmentDark, fontFamily: "inherit", fontSize: 12 }}
                  onMouseEnter={e => e.currentTarget.style.background = "rgba(201,168,76,0.12)"}
                  onMouseLeave={e => e.currentTarget.style.background = "rgba(245,236,215,0.04)"}>
                  <div style={{ color: COLORS.gold, fontWeight: 600, fontSize: 12 }}>{f.name}</div>
                  <div style={{ fontSize: 11, marginTop: 1 }}>{f.title}</div>
                </button>
              ))}
            </div>
          </div>
          <DragHandle onMouseDown={refPanel.onMouseDown} />
        </>)}

        {showReference && (<>
          <div style={{ width: refPanel.width, display: "flex", flexDirection: "column", background: "rgba(0,0,0,0.3)", overflow: "hidden", flexShrink: 0 }}>
            <div style={{ display: "flex", borderBottom: `1px solid ${COLORS.goldDim}22` }}>
              {[["postulates", "Post."], ["notions", "C.N."], ["definitions", "Def."]].map(([tab, label]) => (
                <button key={tab} onClick={() => setRefTab(tab)} style={{ flex: 1, padding: "8px 4px", background: refTab === tab ? "rgba(201,168,76,0.15)" : "transparent", border: "none", borderBottom: refTab === tab ? `2px solid ${COLORS.gold}` : "2px solid transparent", color: refTab === tab ? COLORS.gold : COLORS.parchmentDark, cursor: "pointer", fontFamily: "inherit", fontSize: 11 }}>{label}</button>
              ))}
            </div>
            <div style={{ flex: 1, overflow: "auto", padding: 8 }}>
              {(refTab === "postulates" ? POSTULATES : refTab === "notions" ? COMMON_NOTIONS : DEFINITIONS).map(item => (
                <div key={item.id} style={{ marginBottom: 8, padding: "6px 8px", background: "rgba(245,236,215,0.03)", borderRadius: 4, borderLeft: `2px solid ${COLORS.goldDim}44` }}>
                  <div style={{ color: COLORS.gold, fontSize: 11, fontWeight: 700 }}>{item.id}</div>
                  <div style={{ color: COLORS.parchmentDark, fontSize: 12, lineHeight: 1.4, marginTop: 2 }}>{item.text}</div>
                </div>
              ))}
            </div>
          </div>
          <DragHandle onMouseDown={refPanel.onMouseDown} />
        </>)}

        {/* ── Canvas Area ── */}
        <div style={{ flex: 1, display: "flex", flexDirection: "column", minWidth: 200, overflow: "hidden" }}>
          {/* Toolbar */}
          <div style={{ display: "flex", alignItems: "center", gap: 3, padding: "5px 8px", background: "rgba(0,0,0,0.25)", borderBottom: `1px solid ${COLORS.goldDim}22`, flexShrink: 0, flexWrap: "wrap" }}>
            {toolButtons.map(t => (
              <button key={t.id} onClick={() => { setTool(t.id); setPendingClick(null); }}
                style={{ padding: "4px 9px", background: tool === t.id ? COLORS.gold : "rgba(245,236,215,0.06)", color: tool === t.id ? COLORS.ink : COLORS.parchmentDark, border: `1px solid ${tool === t.id ? COLORS.gold : COLORS.goldDim + "33"}`, borderRadius: 3, cursor: "pointer", fontFamily: "inherit", fontSize: 12, fontWeight: tool === t.id ? 700 : 400 }}>
                <span style={{ marginRight: 3 }}>{t.icon}</span>{t.label}
              </button>
            ))}
            {/* Color picker */}
            <div style={{ display: "flex", gap: 2, marginLeft: 8, alignItems: "center" }}>
              <span style={{ fontSize: 10, color: COLORS.parchmentDark + "88", marginRight: 2 }}>Color:</span>
              {LINE_COLORS.map(c => (
                <button key={c.id} onClick={() => setActiveColor(c.hex)} title={c.label}
                  style={{ width: 18, height: 18, borderRadius: "50%", background: c.hex, border: activeColor === c.hex ? `2px solid ${COLORS.gold}` : "2px solid transparent", cursor: "pointer", padding: 0, boxShadow: activeColor === c.hex ? `0 0 4px ${COLORS.gold}88` : "none" }} />
              ))}
            </div>
            <div style={{ flex: 1 }} />
            {statusText && <span style={{ color: COLORS.goldDim, fontSize: 11 }}>{statusText}</span>}
            <button onClick={() => setPendingClick(null)} style={{ ...btnStyle(), background: "transparent", color: COLORS.parchmentDark + "88", fontSize: 11, display: pendingClick ? "block" : "none" }}>Cancel</button>
            <button onClick={clearCanvas} style={{ ...btnStyle(), background: "rgba(139,37,0,0.2)", border: `1px solid ${COLORS.red}44`, color: COLORS.red }}>Clear All</button>
          </div>

          {/* Canvas */}
          <div ref={canvasWrapRef} style={{ flex: 1, position: "relative", overflow: "hidden" }}>
            <canvas ref={canvasRef}
              style={{ display: "block", width: "100%", height: "100%", cursor: "crosshair" }}
              onClick={handleCanvasClick} onMouseMove={handleCanvasMove} />
            {currentFile?.diagramHint && (
              <div style={{ position: "absolute", bottom: 8, left: 8, right: 8, padding: "6px 10px", background: "rgba(44,24,16,0.88)", borderRadius: 4, fontSize: 11, color: COLORS.parchmentDark, lineHeight: 1.4, pointerEvents: "none" }}>
                <strong style={{ color: COLORS.goldDim }}>Hint: </strong>{currentFile.diagramHint}
              </div>
            )}
          </div>
        </div>

        {/* ── Journal Panel (right, resizable) ── */}
        <DragHandle onMouseDown={journalPanel.onMouseDown} side="right" />
        <div style={{ width: journalPanel.width, display: "flex", flexDirection: "column", background: "rgba(0,0,0,0.15)", flexShrink: 0, overflow: "hidden" }}>
          <div style={{ padding: "8px 12px", borderBottom: `1px solid ${COLORS.goldDim}22`, display: "flex", justifyContent: "space-between", alignItems: "center", flexShrink: 0 }}>
            <h3 style={{ margin: 0, fontSize: 12, color: COLORS.gold, letterSpacing: 2, textTransform: "uppercase" }}>Proof Journal</h3>
            <button onClick={addJournalStep} style={{ padding: "3px 10px", background: COLORS.gold, color: COLORS.ink, border: "none", borderRadius: 3, cursor: "pointer", fontFamily: "inherit", fontSize: 11, fontWeight: 700 }}>+ Step</button>
          </div>

          <div style={{ flex: 1, overflow: "auto", padding: "6px 8px" }}>
            {journalSteps.length === 0 && (
              <div style={{ textAlign: "center", color: COLORS.parchmentDark + "55", fontSize: 13, padding: 24, fontStyle: "italic" }}>
                No steps yet. Draw on the canvas or click "+ Step" to begin.
              </div>
            )}
            {journalSteps.map((step, i) => (
              <div key={i} style={{ marginBottom: 6, padding: "7px 9px", background: "rgba(245,236,215,0.04)", border: `1px solid ${COLORS.goldDim}22`, borderRadius: 4, fontSize: 12 }}>
                <div style={{ display: "flex", justifyContent: "space-between", alignItems: "center", marginBottom: 3 }}>
                  <span style={{ color: COLORS.gold, fontSize: 11, fontWeight: 700 }}>Step {i + 1}</span>
                  <div style={{ display: "flex", gap: 2 }}>
                    <button onClick={() => moveStep(i, -1)} disabled={i === 0} style={{ ...tinyBtn(), opacity: i === 0 ? 0.3 : 1 }}>▲</button>
                    <button onClick={() => moveStep(i, 1)} disabled={i === journalSteps.length - 1} style={{ ...tinyBtn(), opacity: i === journalSteps.length - 1 ? 0.3 : 1 }}>▼</button>
                    <button onClick={() => removeStep(i)} style={{ ...tinyBtn(), color: COLORS.red }}>✕</button>
                  </div>
                </div>
                <textarea value={step.text} onChange={e => updateStep(i, "text", e.target.value)} placeholder="Describe the logical step…"
                  rows={2} style={{ ...inputStyle(), resize: "vertical", minHeight: 32 }} />
                <div style={{ display: "flex", gap: 4, marginTop: 3 }}>
                  <select value={step.justification} onChange={e => updateStep(i, "justification", e.target.value)} style={{ ...inputStyle(), flex: 1, padding: "3px 4px", fontSize: 11 }}>
                    <option value="">— Justification —</option>
                    <optgroup label="Postulates">{POSTULATES.map(p => <option key={p.id} value={p.id}>{p.id}</option>)}</optgroup>
                    <optgroup label="Common Notions">{COMMON_NOTIONS.map(c => <option key={c.id} value={c.id}>{c.id}</option>)}</optgroup>
                    <optgroup label="Definitions">{DEFINITIONS.slice(0, 12).map(d => <option key={d.id} value={d.id}>{d.id}</option>)}</optgroup>
                    <optgroup label="Prior Propositions">{PROOF_FILES.map(p => <option key={p.id} value={p.name.replace("Proposition ", "Prop.")}>{p.name}</option>)}</optgroup>
                    <optgroup label="Other">{["Given", "Construction", "Assumption", "Contradiction", "Substitution"].map(j => <option key={j} value={j}>{j}</option>)}</optgroup>
                  </select>
                  <input value={step.justification} onChange={e => updateStep(i, "justification", e.target.value)} placeholder="or type…"
                    style={{ ...inputStyle(), width: 80, padding: "3px 5px", fontSize: 11, flexShrink: 0 }} />
                </div>
              </div>
            ))}
          </div>

          {/* Conclusion + Verify */}
          <div style={{ padding: "8px 10px", borderTop: `1px solid ${COLORS.goldDim}22`, background: "rgba(201,168,76,0.04)", flexShrink: 0 }}>
            <div style={{ fontSize: 10, color: COLORS.goldDim, letterSpacing: 1, marginBottom: 3, textTransform: "uppercase" }}>Conclusion</div>
            <textarea value={conclusionText} onChange={e => setConclusionText(e.target.value)} placeholder="State your Q.E.D. claim…"
              rows={2} style={{ ...inputStyle(), color: COLORS.gold, fontStyle: "italic", borderColor: COLORS.gold + "44", resize: "vertical", minHeight: 36 }} />
            <button onClick={verifyProof}
              style={{ width: "100%", marginTop: 6, padding: "9px", background: `linear-gradient(135deg, ${COLORS.gold}, ${COLORS.goldBright})`, color: COLORS.ink, border: "none", borderRadius: 4, cursor: "pointer", fontFamily: "inherit", fontSize: 14, fontWeight: 700, letterSpacing: 1 }}>
              ✦ VERIFY PROOF
            </button>
            {verificationResult && (
              <div style={{ marginTop: 8, padding: 8, background: verificationResult.type === "success" ? "rgba(45,90,39,0.2)" : verificationResult.type === "info" ? "rgba(26,58,92,0.2)" : "rgba(139,37,0,0.15)", border: `1px solid ${(verificationResult.type === "success" ? COLORS.green : verificationResult.type === "info" ? COLORS.blue : COLORS.red) + "44"}`, borderRadius: 4 }}>
                {verificationResult.type === "info" ? (
                  <div style={{ color: COLORS.parchmentDark, fontSize: 12 }}>{verificationResult.message}</div>
                ) : (<>
                  <div style={{ color: verificationResult.allSatisfied ? COLORS.green : COLORS.red, fontSize: 13, fontWeight: 700, marginBottom: 4 }}>
                    {verificationResult.allSatisfied ? "✓ Proof Verified — Q.E.D." : "✗ Proof Incomplete"}
                  </div>
                  <div style={{ maxHeight: 130, overflow: "auto" }}>
                    {verificationResult.results.map((r, i) => (
                      <div key={i} style={{ fontSize: 11, padding: "2px 0", color: (r.satisfied ? COLORS.green : COLORS.red) + "cc", display: "flex", gap: 5 }}>
                        <span>{r.satisfied ? "✓" : "✗"}</span>
                        <span style={{ flex: 1 }}>Step {r.step}: {r.keywords.join(", ")}{r.required ? ` [${r.required}]` : ""}</span>
                      </div>
                    ))}
                  </div>
                </>)}
              </div>
            )}
          </div>
        </div>
      </div>
    </div>
  );
}

// Style helpers
function btnStyle() {
  return { padding: "4px 11px", border: `1px solid ${COLORS.goldDim}44`, borderRadius: 4, color: COLORS.gold, cursor: "pointer", fontFamily: "inherit", fontSize: 12 };
}
function tinyBtn() {
  return { background: "none", border: "none", color: COLORS.parchmentDark, cursor: "pointer", fontSize: 11, padding: "0 3px", fontFamily: "inherit" };
}
function inputStyle() {
  return { width: "100%", boxSizing: "border-box", padding: "5px 7px", background: "rgba(0,0,0,0.2)", border: `1px solid ${COLORS.goldDim}22`, borderRadius: 3, color: COLORS.parchment, fontFamily: "inherit", fontSize: 12, outline: "none" };
}
