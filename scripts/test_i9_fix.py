import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
os.environ['PYTHONIOENCODING'] = 'utf-8'
from scripts.real_proofs import PB
from verifier.unified_checker import verify_e_proof_json

premises = ['\u00ac(a = b)', '\u00ac(a = c)', '\u00ac(b = c)', 'on(a, M)', 'on(b, M)', 'on(a, N)', 'on(c, N)', '\u00ac(on(c, M))', '\u00ac(on(b, N))']
goal = '\u2220bae = \u2220cae, same-side(e, c, M), same-side(e, b, N)'

pb = PB('test-I9-fix', premises, goal)
gids = pb.auto_given()
pb.s('center(a, \u03b1), on(b, \u03b1)', 'let-circle', [1])
pb.s('inside(a, \u03b1)', 'Generality 3', [10])
pb.s('on(d, \u03b1), on(d, N), between(d, a, c)', 'let-intersection-line-circle-extend', [11, 6, 2, 7])
pb.s('on(f, \u03b1), on(f, M), between(f, a, b)', 'let-intersection-line-circle-extend', [11, 4, 1, 5])
pb.s('ad = ab', 'Segment transfer 3b', [10, 12])
pb.s('af = ab', 'Segment transfer 3b', [10, 13])
pb.s('ad = af', 'CN1 \u2014 Transitivity', [14, 15])
pb.s('\u00ac(d = a)', 'Betweenness 1b', [12])
pb.s('\u00ac(M = N)', 'Generality 5', [5, 9])
pb.s('\u00ac(on(d, M))', 'Generality 1', [4, 6, 12, 17, 18])
pb.s('\u00ac(f = a)', 'Betweenness 1b', [13])
pb.s('\u00ac(on(f, N))', 'Generality 1', [4, 6, 13, 20, 18])
pb.s('\u00ac(f = d)', 'Generality 6', [13, 19])
pb.s('center(d, \u03b2), on(f, \u03b2)', 'let-circle', [22])
pb.s('center(f, \u03b3), on(d, \u03b3)', 'let-circle', [22])
pb.s('inside(d, \u03b2)', 'Generality 3', [23])
pb.s('inside(f, \u03b3)', 'Generality 3', [24])
pb.s('intersects(\u03b2, \u03b3)', 'Intersection 5', [23, 24, 25, 26])
pb.s('on(d, K), on(f, K)', 'let-line', [22])
pb.s('on(e, \u03b2), on(e, \u03b3), \u00ac(same-side(e, a, K)), \u00ac(on(e, K))', 'let-intersection-circle-circle-opposite-side', [27, 23, 24, 28, 12, 13, 5, 6, 9, 17, 18, 19, 4])
pb.s('de = df', 'Segment transfer 3b', [23, 29])
pb.s('fe = fd', 'Segment transfer 3b', [24, 29])
pb.s('df = fd', 'M3 \u2014 Symmetry', [])
pb.s('de = fe', 'CN1 \u2014 Transitivity', [30, 31, 32])
pb.s('\u00ac(e = d)', 'Generality 6', [28, 29])
pb.s('\u00ac(e = f)', 'Generality 6', [28, 29])
pb.s('\u00ac(a = e)', 'Same-side 6', [29, 28, 6, 12, 17, 18])
pb.s('ae = ae', 'CN4 \u2014 Reflexivity', [])
pb.s('\u2220dae = \u2220fae, \u2220ade = \u2220afe, \u2220aed = \u2220aef, \u25b3ade = \u25b3afe', 'SSS', [16, 33, 37])
pb.s('\u00ac(K = M)', 'Generality 5', [28, 19])
pb.s('\u00ac(K = N)', 'Generality 5', [28, 21])

# REDUCTIO: not-on(e, M)
pb._depth = 1; pb._lid = 40
pb._lines.append({'id': 41, 'depth': 1, 'statement': 'on(e, M)', 'justification': 'Assume', 'refs': []})
pb._lid = 41
pb.s('between(a, f, e)', 'Pasch 4', [39, 28, 13, 4, 41, 20, 35, 29])
pb.s('between(b, a, f)', 'Betweenness 1a', [13])
pb.s('between(b, a, e)', 'Betweenness 5', [43, 42])
pb.s('\u00ac(between(a, f, e))', 'Betweenness 7', [43, 44])
pb.s('\u22a5', '\u22a5-intro', [42, 45])
pb._depth = 0; pb._lid = 46
pb._lines.append({'id': 47, 'depth': 0, 'statement': '\u00ac(on(e, M))', 'justification': '\u22a5-elim', 'refs': [41]})
pb._lid = 47

# REDUCTIO: not-on(e, N)
pb._depth = 1
pb._lines.append({'id': 48, 'depth': 1, 'statement': 'on(e, N)', 'justification': 'Assume', 'refs': []})
pb._lid = 48
pb.s('between(a, d, e)', 'Pasch 4', [40, 28, 12, 6, 48, 17, 34, 29])
pb.s('between(c, a, d)', 'Betweenness 1a', [12])
pb.s('between(c, a, e)', 'Betweenness 5', [50, 49])
pb.s('\u00ac(between(a, d, e))', 'Betweenness 7', [50, 51])
pb.s('\u22a5', '\u22a5-intro', [49, 52])
pb._depth = 0; pb._lid = 53
pb._lines.append({'id': 54, 'depth': 0, 'statement': '\u00ac(on(e, N))', 'justification': '\u22a5-elim', 'refs': [48]})
pb._lid = 54

# not-on(a, K) via G1
pb.s('\u00ac(on(a, K))', 'Generality 1', [6, 12, 28, 17, 40])           # 55

# P2: between(d,a,c), on(d,K), not-on(a,K) -> ss(a,c,K)
pb.s('same-side(a, c, K)', 'Pasch 2', [12, 28, 55])                     # 56
# P2: between(f,a,b), on(f,K), not-on(a,K) -> ss(a,b,K)
pb.s('same-side(a, b, K)', 'Pasch 2', [13, 28, 55])                     # 57

# P3: between(d,a,c), on(a,M) -> not-ss(d,c,M)
pb.s('\u00ac(same-side(d, c, M))', 'Pasch 3', [12, 4])                  # 58
# P3: between(f,a,b), on(a,N) -> not-ss(f,b,N)
pb.s('\u00ac(same-side(f, b, N))', 'Pasch 3', [13, 6])                  # 59

# Now try TI1: L=K, M=M, N=N, all meet at... wait, K doesn't pass through a.
# TI1 needs on(a,L), on(a,M), on(a,N) - three lines through one point.
# We need a line through a. Let's use L (line through a, e).
# Wait, we construct L through a,e at some later step.
# For now let me try a different line configuration.

# What about constructing line L through a, e?
pb.s('on(a, L), on(e, L)', 'let-line', [36])                            # 60

# Now three lines L,M,N meet at a: on(a,L), on(a,M), on(a,N).
# For TI1: on(b_ti,L), on(c_ti,M), on(d_ti,N).
# b_ti on L: e is on L. c_ti on M: b or f is on M. d_ti on N: c or d is on N.

# TI1 with b=e(on L), c=f(on M), d=d(on N):
# ss(f,d,L) and ss(e,f,N) -> not-ss(e,d,M)
# Do we have ss(f,d,L)? f and d same side of L (through a,e)
# Do we have ss(e,f,N)? e and f same side of N (through a,c)
# These are not directly available...

# TI1 with b=e(on L), c=f(on M), d=c(on N):
# ss(f,c,L) and ss(e,f,N) -> not-ss(e,c,M)
# not-ss(e,c,M) is the NEGATION of what we want!

# TI1 with b=e(on L), c=b(on M), d=d(on N):
# ss(b,d,L) and ss(e,b,N) -> not-ss(e,d,M)
# ss(e,b,N) is one of our goals - can't use.

# TI1 with b=e(on L), c=b(on M), d=c(on N):
# ss(b,c,L) and ss(e,b,N) -> not-ss(e,c,M) 
# Again not-ss(e,c,M) is wrong direction, and ss(e,b,N) is a goal.

# Let me try TI2 instead.
# TI2: on(a,L), on(a,M), on(a,N), on(b,L), on(c,M), on(d,N),
#      ss(c,d,L), not-ss(b,d,M), not-on(d,M), b!=a -> ss(b,c,N)
# We want ss(e,c,M). TI2 concludes ss(b,c,N).
# To get ss(e,c,M), set N=M: ss(b,c,M). With b=e, c=c:
# Set L=K or L=L_ae? Hmm this is getting circular.

# Let me just try SS5 with more deps, including the P2 results:
# SS5 a=e,b=d,c=c,L=M: need not-ss(e,d,M). The consequence engine
# should be able to derive this if we give it enough deps.
# What facts could imply not-ss(e,d,M)?
# From not-ss(e,a,K) and same-side(a,c,K) and same-side(a,b,K)...

# Actually, let me try using SS5 directly with all relevant deps and see:
pb.s('same-side(e, c, M)', 'Same-side 5', [19, 47, 8, 58, 29, 28, 12, 13, 4, 6, 55, 56, 57])
pb.s('same-side(e, b, N)', 'Same-side 5', [21, 54, 9, 59, 29, 28, 12, 13, 4, 6, 55, 56, 57])

proof = pb.build()
res = verify_e_proof_json(proof)
for k in sorted(res.line_results):
    r2 = res.line_results[k]
    st = 'OK' if r2.valid else 'FAIL'
    errs = r2.errors if not r2.valid else ''
    print(f'L{k}: {st} {errs}')
print()
print(f'accepted={res.accepted}')