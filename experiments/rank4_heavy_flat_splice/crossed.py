"""The core of the P-cycle local lemma: not every valid split of S is crossed.

Rank 4, 8 elements: A0 = {a, ab}, A1 = {b, bb} with A0 + A1 a basis; S = {u, v, w, z} a basis.
An ordered split (P, Q) of S (|P| = 2) is valid if A0 + P and Q + A1 are bases. It is crossed if
P = {p, p'} with p || b and p' || bb in M / A0, and p || bb and p' || b in M / Q (|| = parallel,
i.e. {p, b} + A0 has rank 3, and so on).

Given that (P, Q) = ({u, v}, {w, z}) is valid and crossed with u || b, v || bb in M / A0, this script
reports, for every other ordered split, whether it is forced valid, forced invalid, forced crossed,
forced not crossed, or free. With "claim", it checks that some valid split is not crossed.

Usage: python crossed.py [claim]
"""
import itertools, sys
from pysat.solvers import Cadical195

n, r = 8, 4
var = lambda X, v: 5 * X + v
pc = lambda X: bin(X).count("1")
mask = lambda c: sum(1 << x for x in c)
u, v, w, z, a, ab, b, bb = range(8)
S = [u, v, w, z]
A0, A1 = (a, ab), (b, bb)
names = ["u", "v", "w", "z", "a", "ab", "b", "bb"]

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
Bs = lambda xs: var(mask(xs), 4)
cls += [[Bs(S)], [Bs(A0 + A1)]]

nv = [5 * (1 << n) + 10]


def new():
    nv[0] += 1
    return nv[0]


def valid_lit(P, Q):
    g = new()
    cls.append([-g, Bs(P + A0)])
    cls.append([-g, Bs(Q + A1)])
    cls.append([g, -Bs(P + A0), -Bs(Q + A1)])
    return g


def crossed_lit(P, Q):
    """crossed: for one labelling (p, p') of P: p||b, p'||bb in M/A0 and p||bb, p'||b in M/Q."""
    g = new()
    opts = []
    for p, pp in (P, P[::-1]):
        h = new()
        conds = [-Bs((p, b) + A0), -Bs((pp, bb) + A0), -Bs((p, bb) + Q), -Bs((pp, b) + Q)]
        for c in conds:
            cls.append([-h, c])
        cls.append([h] + [-c for c in conds])
        opts.append(h)
    cls.append([-g] + opts)
    for h in opts:
        cls.append([g, -h])
    return g


splits = []
for P in itertools.combinations(S, 2):
    Q = tuple(s for s in S if s not in P)
    splits += [(P, Q)]
lits = {sp: (valid_lit(*sp), crossed_lit(*sp)) for sp in splits}
base = ((u, v), (w, z))
cls.append([lits[base][0]])
cls += [[-Bs((u, b) + A0)], [-Bs((v, bb) + A0)], [-Bs((u, bb) + (w, z))], [-Bs((v, b) + (w, z))]]

s = Cadical195(bootstrap_with=cls)
if "claim" in sys.argv:
    s2 = Cadical195(bootstrap_with=cls[:-5] if False else cls)
    ok = all(s.solve(assumptions=[]) for _ in [0])
    # claim: some valid split not crossed. Negation: every split is invalid or crossed.
    s3 = Cadical195(bootstrap_with=cls + [[-lits[sp][0], lits[sp][1]] for sp in splits])
    print("every valid split crossed is", "possible (SAT)" if s3.solve() else "impossible (UNSAT)")
    sys.exit()
fmt = lambda sp: "{" + "".join(names[x] for x in sp[0]) + "|" + "".join(names[x] for x in sp[1]) + "}"
for sp in splits:
    vl, cl = lits[sp]
    fv = "valid" if not s.solve(assumptions=[-vl]) else ("invalid" if not s.solve(assumptions=[vl]) else "?")
    fc = "crossed" if not s.solve(assumptions=[vl, -cl]) else (
        "not crossed" if not s.solve(assumptions=[vl, cl]) else "?")
    print(f"  {fmt(sp)}: {fv}; if valid: {fc}")
