"""The local lemma behind pair-chain insertion (XP), rank 4, 12 elements, exact.

Pairs around the insertion point, oriented as in sigma: A_{-1} = (x, xb), A_0 = (a, ab),
A_1 = (b, bb), A_2 = (y, yb); S = {s0, s1, s2, s3} a basis. Hypotheses: A_{-1}+A_0, A_0+A_1,
A_1+A_2 bases; the sigma windows {xb, a, ab, b} and {ab, b, bb, y} bases. "tightm1" makes
R_{-1} (A_{-1} -> A_1 through A_0) a permutation, "tight0" makes R_0 (A_0 -> A_2 through A_1)
one.

Insert P, Q (S = P + Q, ordered split) between A_0 and A_1; valid if A_0 + P and Q + A_1 are
bases. The four new windows:
  Wa = {last A_{-1}} + A_0 + {first P}      Wb = {last A_0} + P + {first Q}
  Wc = {last P} + Q + {first A_1}           Wd = {last Q} + A_1 + {first A_2}
Old pairs may flip along the paths left when R_{-1} and R_0 are removed (their other relations
are permutations):
  odd   (one cycle, m odd):  A_{-1} with A_2 (flip e1), A_0 with A_1 (flip e2);
  even  (two cycles, m even): A_{-1} with A_1 (flip e1), A_0 with A_2 (flip e2);
  Ponly (m even, only the cycle through P must close): Wa and Wc, flip A_{-1} with A_1;
  Qonly (m even, only the cycle through Q must close): Wb and Wd, flip A_0 with A_2.
Claim: some valid split, orientations and flips make the required windows bases.

Usage: python local_xp.py odd|even|Ponly|Qonly [tightm1] [tight0] [show]
"""
import itertools, sys, time
from pysat.solvers import Cadical195

mode = sys.argv[1]
opts = sys.argv[2:]
n, r = 12, 4
var = lambda X, v: 5 * X + v
pc = lambda X: bin(X).count("1")
mask = lambda c: sum(1 << x for x in c)
S = [0, 1, 2, 3]
x, xb, a, ab, b, bb, y, yb = range(4, 12)
Am1, A0, A1, A2 = (x, xb), (a, ab), (b, bb), (y, yb)

cls = []
for X in range(1 << n):
    for v in range(1, r):
        cls.append([-var(X, v + 1), var(X, v)])
    for v in range(pc(X) + 1, r + 1):
        cls.append([-var(X, v)])
    if pc(X) >= 1:
        cls.append([var(X, 1)])
for X in range(1 << n):
    for p in range(n):
        if X >> p & 1:
            continue
        T = X | 1 << p
        for v in range(1, r + 1):
            cls.append([-var(X, v), var(T, v)])
            if v < r:
                cls.append([-var(T, v + 1), var(X, v)])
        for q in range(p + 1, n):
            if X >> q & 1:
                continue
            U, Xq = T | 1 << q, X | 1 << q
            for v in range(1, r + 1):
                c = [-var(U, v), var(T, v), var(Xq, v), var(X, v)]
                if v >= 2:
                    c.append(-var(X, v - 1))
                cls.append(c)
Bs = lambda xs: var(mask(xs), 4)
for W in (S, Am1 + A0, A0 + A1, A1 + A2, (xb, a, ab, b), (ab, b, bb, y)):
    cls.append([Bs(W)])
if "tightm1" in opts:          # R_{-1} a permutation: (x, bb) entry, (xb, bb) and (x, b) not
    cls += [[Bs((x, a, ab, bb))], [-Bs((xb, a, ab, bb))], [-Bs((x, a, ab, b))]]
if "tight0" in opts:           # R_0 a permutation: (a, yb) entry, (ab, yb) and (a, y) not
    cls += [[Bs((a, b, bb, yb))], [-Bs((ab, b, bb, yb))], [-Bs((a, b, bb, y))]]

flip = lambda pair, f: pair if f == 0 else (pair[1], pair[0])
first = lambda pair: pair[0]
last = lambda pair: pair[1]
for Pu in itertools.combinations(S, 2):
    Qu = tuple(s for s in S if s not in Pu)
    valid = [Bs(A0 + Pu), Bs(Qu + A1)]
    for oP, oQ, e1, e2 in itertools.product((0, 1), repeat=4):
        P, Q = flip(Pu, oP), flip(Qu, oQ)
        if mode == "odd":
            m1, m0, p1, p2 = flip(Am1, e1), flip(A0, e2), flip(A1, e2), flip(A2, e1)
        else:
            m1, m0, p1, p2 = flip(Am1, e1), flip(A0, e2), flip(A1, e1), flip(A2, e2)
        Wa = (last(m1),) + A0 + (first(P),)
        Wb = (last(m0),) + Pu + (first(Q),)
        Wc = (last(P),) + Qu + (first(p1),)
        Wd = (last(Q),) + A1 + (first(p2),)
        need = {"odd": [Wa, Wb, Wc, Wd], "even": [Wa, Wb, Wc, Wd],
                "Ponly": [Wa, Wc], "Qonly": [Wb, Wd]}[mode]
        # valid -> some required window fails
        cls.append([-v for v in valid] + [-Bs(W) for W in need])

if "write" in opts:
    import os
    from cert_measure import OUT
    name = "localxp_" + "_".join([mode] + sorted(o for o in opts if o not in ("write", "show")))
    with open(os.path.join(OUT, name + ".cnf"), "w", newline="\n") as f:
        f.write(f"p cnf {max(abs(l) for c in cls for l in c)} {len(cls)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    print("wrote", name)
t = time.time()
s = Cadical195(bootstrap_with=cls)
res = s.solve()
print(f"local XP {mode} {opts}: {'SAT (fails)' if res else 'UNSAT (holds)'} ({time.time() - t:.1f}s)")
if res and "show" in opts:
    model = set(l for l in s.get_model() if l > 0)
    rk = lambda X: max([v for v in range(1, 5) if var(X, v) in model], default=0)
    names = ["s0", "s1", "s2", "s3", "x", "xb", "a", "ab", "b", "bb", "y", "yb"]
    for rank_ in (1, 2, 3):
        fl = []
        for X in range(1, 1 << n):
            if rk(X) == rank_ and pc(X) > rank_ and all(rk(X | 1 << e) > rank_ for e in range(n)
                                                        if not X >> e & 1):
                fl.append(" ".join(names[e] for e in range(n) if X >> e & 1))
        print(f"  rank-{rank_} flats with extra elements:", fl)
