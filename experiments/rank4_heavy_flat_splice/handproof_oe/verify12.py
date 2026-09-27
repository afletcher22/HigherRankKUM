"""Sanity check (SAT) of the reduction in PROOF.md Steps 1-3, on the exact 12-element model of
local_xp.py with tightm1 + tight0: for every ordered split (P, Q) of S,
   [valid and no (oP, oQ, e1, e2) makes the four windows bases]
   <=>  EVEN: P-crossed or Q-crossed;
        ODD : all four matchings exist and exactly one of P-crossed, Q-crossed.
Also: 'valid, neither crossed' -> some assignment works (both modes)."""
import itertools, sys
from pysat.solvers import Cadical195
sys.argv = ["x"]
from m8 import base_clauses, var, mask, pc
n = 12
S = [0, 1, 2, 3]
x, xb, a, ab, b, bb, y, yb = range(4, 12)
Am1, A0, A1, A2 = (x, xb), (a, ab), (b, bb), (y, yb)
Bs = lambda xs: var(mask(xs), 4)
cls = base_clauses(12)
for W in (S, Am1 + A0, A0 + A1, A1 + A2, (xb, a, ab, b), (ab, b, bb, y)):
    cls.append([Bs(W)])
cls += [[Bs((x, a, ab, bb))], [-Bs((xb, a, ab, bb))], [-Bs((x, a, ab, b))]]
cls += [[Bs((a, b, bb, yb))], [-Bs((ab, b, bb, yb))], [-Bs((a, b, bb, y))]]
nv = [5 * (1 << n) + 10]
def new():
    nv[0] += 1; return nv[0]
def AND(ls):
    g = new(); [cls.append([-g, l]) for l in ls]; cls.append([g] + [-l for l in ls]); return g
def OR(ls):
    g = new(); cls.append([-g] + list(ls)); [cls.append([g, -l]) for l in ls]; return g
par = lambda ctx, s, t: -Bs(tuple(ctx) + (s, t))
def matching(ctx, X, Y):
    """returns (exists, straight, twisted): straight X0||Y0, X1||Y1 ; twisted X0||Y1, X1||Y0"""
    st = AND([par(ctx, X[0], Y[0]), par(ctx, X[1], Y[1])])
    tw = AND([par(ctx, X[0], Y[1]), par(ctx, X[1], Y[0])])
    return OR([st, tw]), st, tw
flip = lambda pair, f: pair if f == 0 else (pair[1], pair[0])
res = {}
for mode in ("even", "odd"):
    for Pu in itertools.combinations(S, 2):
        Qu = tuple(s for s in S if s not in Pu)
        valid = AND([Bs(A0 + Pu), Bs(Qu + A1)])
        good = []
        for oP, oQ, e1, e2 in itertools.product((0, 1), repeat=4):
            P, Q = flip(Pu, oP), flip(Qu, oQ)
            if mode == "odd":
                m1, m0, p1, p2 = flip(Am1, e1), flip(A0, e2), flip(A1, e2), flip(A2, e1)
            else:
                m1, m0, p1, p2 = flip(Am1, e1), flip(A0, e2), flip(A1, e1), flip(A2, e2)
            Wa = (m1[1],) + A0 + (P[0],)
            Wb = (m0[1],) + Pu + (Q[0],)
            Wc = (P[1],) + Qu + (p1[0],)
            Wd = (Q[1],) + A1 + (p2[0],)
            good.append(AND([Bs(W) for W in (Wa, Wb, Wc, Wd)]))
        solvable = OR(good)
        al, al_s, al_t = matching(A0, Pu, A1)
        ga, ga_s, ga_t = matching(Qu, Pu, A1)
        be, be_s, be_t = matching(Pu, Qu, A0)
        de, de_s, de_t = matching(A1, Qu, A0)
        Pc = OR([AND([al_s, ga_t]), AND([al_t, ga_s])])
        Qc = OR([AND([be_s, de_t]), AND([be_t, de_s])])
        if mode == "even":
            bad = OR([Pc, Qc])
        else:
            x1 = new(); cls.extend([[-x1, Pc, Qc], [-x1, -Pc, -Qc], [x1, -Pc, Qc], [x1, Pc, -Qc]])
            bad = AND([al, ga, be, de, x1])
        res[(mode, Pu)] = (valid, solvable, bad, Pc, Qc)
s = Cadical195(bootstrap_with=cls)
print("base consistent:", s.solve())
ok = True
for (mode, Pu), (valid, solvable, bad, Pc, Qc) in res.items():
    r1 = s.solve(assumptions=[valid, -solvable, -bad])
    r2 = s.solve(assumptions=[valid, solvable, bad])
    r3 = s.solve(assumptions=[valid, -Pc, -Qc, -solvable])
    print(mode, Pu, "unsolvable&~bad:", r1, " solvable&bad:", r2, " uncrossed&unsolvable:", r3)
    ok &= not (r1 or r2 or r3)
print("characterization verified:", ok)
print("Controls (should be SAT: the bad situations do occur for a single split):")
for mode in ("even", "odd"):
    valid, solvable, bad, Pc, Qc = res[(mode, (0, 1))]
    print(" ", mode, "valid & unsolvable:", s.solve(assumptions=[valid, -solvable]),
          "| valid & P-crossed:", s.solve(assumptions=[valid, Pc]),
          "| valid & Q-crossed:", s.solve(assumptions=[valid, Qc]))
