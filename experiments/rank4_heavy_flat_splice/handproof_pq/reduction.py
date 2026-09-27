"""SAT checks of the reductions in PROOF.md, on 10 elements with the MINIMAL hypotheses used.

P-only: elements s0..s3, x, xb, a, ab, b, bb. Hypotheses: S, A0+A1, {xb,a,ab,b}, {x,a,ab,bb}
bases; {xb,a,ab,bb}, {x,a,ab,b} dependent.
Q-only: elements s0..s3, a, ab, b, bb, y, yb. Hypotheses: S, A0+A1, {ab,b,bb,y}, {a,b,bb,yb}
bases; {ab,b,bb,yb}, {a,b,bb,y} dependent.
"""
import itertools
from pysat.solvers import Cadical195

n, r = 10, 4
var = lambda X, k: 5 * X + k
pc = lambda X: bin(X).count("1")
mask = lambda c: sum(1 << x for x in c)


def axioms():
    cls = []
    for X in range(1 << n):
        for k in range(1, r):
            cls.append([-var(X, k + 1), var(X, k)])
        for k in range(pc(X) + 1, r + 1):
            cls.append([-var(X, k)])
        if pc(X) >= 1:
            cls.append([var(X, 1)])
    for X in range(1 << n):
        for p in range(n):
            if X >> p & 1:
                continue
            T = X | 1 << p
            for k in range(1, r + 1):
                cls.append([-var(X, k), var(T, k)])
                if k < r:
                    cls.append([-var(T, k + 1), var(X, k)])
            for q in range(p + 1, n):
                if X >> q & 1:
                    continue
                U, Xq = T | 1 << q, X | 1 << q
                for k in range(1, r + 1):
                    c = [-var(U, k), var(T, k), var(Xq, k), var(X, k)]
                    if k >= 2:
                        c.append(-var(X, k - 1))
                    cls.append(c)
    return cls


AX = axioms()
Bs = lambda xs: var(mask(xs), 4)
S = (0, 1, 2, 3)
nv = [5 * (1 << n) + 10]


def new():
    nv[0] += 1
    return nv[0]


def AND(lits, cls):
    g = new()
    cls += [[-g, l] for l in lits] + [[g] + [-l for l in lits]]
    return g


def OR(lits, cls):
    g = new()
    cls += [[-g] + lits] + [[g, -l] for l in lits]
    return g


def splits():
    for Pu in itertools.combinations(S, 2):
        yield Pu, tuple(s for s in S if s not in Pu)


# ---------------- P-only ----------------
x, xb, a, ab, b, bb = range(4, 10)
A0, A1 = (a, ab), (b, bb)
hypP = [[Bs(S)], [Bs(A0 + A1)], [Bs((xb, a, ab, b))], [Bs((x, a, ab, bb))],
        [-Bs((xb, a, ab, bb))], [-Bs((x, a, ab, b))]]


def ponly_success(Pu, Qu, cls):
    """literal: some orientation of P and flip make Wa, Wc bases"""
    opts = []
    for p, pb in (Pu, Pu[::-1]):
        for l, f in ((xb, b), (x, bb)):
            opts.append(AND([Bs((l,) + A0 + (p,)), Bs((pb,) + Qu + (f,))], cls))
    return OR(opts, cls)


def crossed(Pu, Qu, cls, a0, a1):
    """P = {p,p'}: p in cl(a0+first a1), p' in cl(a0+last a1), last a1 in cl(Q+p), first a1 in cl(Q+p')"""
    f, l = a1
    opts = []
    for p, pp in (Pu, Pu[::-1]):
        opts.append(AND([-Bs(a0 + (f, p)), -Bs(a0 + (l, pp)), -Bs(Qu + (p, l)), -Bs(Qu + (pp, f))], cls))
    return OR(opts, cls)


cls = AX + hypP
for Pu, Qu in splits():
    sc = ponly_success(Pu, Qu, cls)
    cls.append([-Bs(A0 + Pu), -Bs(Qu + A1), -sc])   # negation: every valid split fails
print("P-only, minimal hypotheses:", "UNSAT (holds)" if not Cadical195(bootstrap_with=cls).solve() else "SAT (fails)")

Pu, Qu = (0, 1), (2, 3)
cls = AX + hypP + [[Bs(A0 + Pu)], [Bs(Qu + A1)]]
sc, cr = ponly_success(Pu, Qu, cls), crossed(Pu, Qu, cls, A0, A1)
print("P-only: valid & fails & not crossed:", "UNSAT (ok)" if not Cadical195(bootstrap_with=cls + [[-sc], [-cr]]).solve() else "SAT (!!)")
print("P-only: valid & crossed & succeeds:", "UNSAT (ok)" if not Cadical195(bootstrap_with=cls + [[sc], [cr]]).solve() else "SAT (!!)")
print("P-only: valid & crossed possible:", Cadical195(bootstrap_with=cls + [[cr]]).solve())

# ---------------- Q-only ----------------
a, ab, b, bb, y, yb = range(4, 10)
A0, A1 = (a, ab), (b, bb)
hypQ = [[Bs(S)], [Bs(A0 + A1)], [Bs((ab, b, bb, y))], [Bs((a, b, bb, yb))],
        [-Bs((ab, b, bb, yb))], [-Bs((a, b, bb, y))]]


def qonly_success(Pu, Qu, cls):
    opts = []
    for q, qb in (Qu, Qu[::-1]):
        for m, f in ((ab, y), (a, yb)):      # e2 = 0: last A0 = ab, first A2 = y; e2 = 1: a, yb
            opts.append(AND([Bs((m,) + Pu + (q,)), Bs((qb,) + A1 + (f,))], cls))
    return OR(opts, cls)


cls = AX + hypQ
for Pu, Qu in splits():
    sc = qonly_success(Pu, Qu, cls)
    cls.append([-Bs(A0 + Pu), -Bs(Qu + A1), -sc])   # negation: every valid split fails
print("Q-only, minimal hypotheses:", "UNSAT (holds)" if not Cadical195(bootstrap_with=cls).solve() else "SAT (fails)")
# mirrored crossing: Q = {q,q'} with q in cl(A1 + ab), q' in cl(A1 + a), a in cl(P+q), ab in cl(P+q')
Pu, Qu = (0, 1), (2, 3)
cls = AX + hypQ + [[Bs(A0 + Pu)], [Bs(Qu + A1)]]
sc, cr = qonly_success(Pu, Qu, cls), crossed(Qu, Pu, cls, A1, (ab, a))
print("Q-only: valid & fails & not mirror-crossed:", "UNSAT (ok)" if not Cadical195(bootstrap_with=cls + [[-sc], [-cr]]).solve() else "SAT (!!)")
print("Q-only: valid & mirror-crossed & succeeds:", "UNSAT (ok)" if not Cadical195(bootstrap_with=cls + [[sc], [cr]]).solve() else "SAT (!!)")
