"""SAT sanity checks of every intermediate claim in PROOF.md (core claim part).

Rank-4 matroids on 8 elements u, v, w, z, a, ab, b, bb (full rank-function encoding, as in
crossed.py). Base hypotheses (H): S = {u,v,w,z} basis, A0 + A1 basis, ({u,v},{w,z}) valid, and
crossed with u in H := cl(A0+b), v in Hb := cl(A0+bb), bb in cl(Q+u), b in cl(Q+v).
Each check: base hypotheses + negation of the claim is UNSAT.
"""
import itertools
from pysat.solvers import Cadical195

n, r = 8, 4
var = lambda X, k: 5 * X + k
pc = lambda X: bin(X).count("1")
mask = lambda c: sum(1 << x for x in c)
u, v, w, z, a, ab, b, bb = range(8)
A0, A1 = (a, ab), (b, bb)

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

indep = lambda xs: var(mask(xs), len(xs))       # literal: xs independent
basis = lambda xs: var(mask(xs), 4)
# e in cl(X) for X independent: X+e dependent
incl = lambda e, X: -indep(tuple(X) + (e,))
nbase = len(cls)
H = lambda e: incl(e, (a, ab, b))       # e in H
Hb = lambda e: incl(e, (a, ab, bb))     # e in Hbar

base = [[basis((u, v, w, z))], [basis(A0 + A1)], [basis(A0 + (u, v))], [basis((w, z) + A1)],
        [H(u)], [Hb(v)], [incl(bb, (u, w, z))], [incl(b, (v, w, z))]]


def unsat(extra, label):
    s = Cadical195(bootstrap_with=cls + base + extra)
    res = s.solve()
    print(f"  {'OK  ' if not res else 'FAIL'} {label}")
    return not res


# crossed-ness literal for a split (P, Q), P a 2-tuple
def crossed_clauses(P, Q, g):
    out, opts = [], []
    for p, pp in (P, P[::-1]):
        h = new()
        conds = [H(p), Hb(pp), incl(bb, Q + (p,)), incl(b, Q + (pp,))]
        out += [[-h, c] for c in conds] + [[h] + [-c for c in conds]]
        opts.append(h)
    out += [[-g] + opts] + [[g, -h] for h in opts]
    return out


nv = [5 * (1 << n) + 10]


def new():
    nv[0] += 1
    return nv[0]


print("Section 3 (basic facts):")
unsat([[-incl(u, (a, ab, u))]] if False else [[Hb(u)]], "u not in Hbar")
unsat([[H(v)]], "v not in H")
unsat([[-basis((x1,) + (a, ab, u))] for x1 in [w]] + [[-H(w)]], "A0+u+w dependent => w in H")
print("Lemma 1:")
unsat([[H(w)], [H(z)]], "not both w,z in H")
unsat([[Hb(w)], [Hb(z)]], "not both w,z in Hbar")
print("Lemma 2:")
unsat([[incl(b, (v, w))], [incl(b, (v, z))]], "not both b in cl(v,w), b in cl(v,z)")
print("Lemma 3:")
for t, o in ((z, w), (w, z)):
    unsat([[-basis((v, t) + A1)], [-incl(b, (v, t))]], f"{{v,{'wz'[t == z]}}}+A1 not basis => b in cl(v,{'wz'[t == z]})")
print("Lemma 4:")
for t in (w, z):
    nm = 'wz'[t == z]
    unsat([[incl(b, (v, t))], [H(t)]], f"b in cl(v,{nm}) => {nm} not in H")
    unsat([[incl(b, (v, t))], [Hb(t)]], f"b in cl(v,{nm}) => {nm} not in Hbar")
    unsat([[incl(bb, (u, t))], [H(t)]], f"bb in cl(u,{nm}) => {nm} not in H")
print("Lemma 5 (C1 crossed => w in Hbar and bb in cl(u,z)); C2 analogous:")
for P, Q, t, o in (((u, w), (v, z), w, z), ((u, z), (v, w), z, w)):
    g = new()
    cc = crossed_clauses(P, Q, g)
    nm, nmo = 'wz'[t == z], 'wz'[o == z]
    unsat(cc + [[g], [-Hb(t)]], f"split {P}|{Q} crossed => {nm} in Hbar")
    unsat(cc + [[g], [-incl(bb, (u, o))]], f"split {P}|{Q} crossed => bb in cl(u,{nmo})")
print("Main theorem (C1 or C2 valid and uncrossed):")
g1, g2 = new(), new()
bad = []
for P, Q, g in (((u, w), (v, z), g1), ((u, z), (v, w), g2)):
    bad += crossed_clauses(P, Q, g)
    bad.append([-basis(A0 + P), -basis(Q + A1), g])   # valid -> crossed
unsat(bad, "C1 or C2 is valid and not crossed")
