"""The hitting lemma at k = 2 (n = 10): does a strict t=0 rank-4 matroid on 10 elements have a
basis B with M - B uniformly dense (6 elements at ratio 6/4)?

Rank function on all 2^10 subsets (variable 5X + v), rank axioms, strict t=0 caps (points <= 2,
lines <= 4, planes <= 6), and for every 4-set B one clause: B is not a basis, or E - B contains
a 2-set of rank <= 1, a 4-set of rank <= 2, or a 5-set of rank <= 3.

Cases: plane6 (elements 0..5 form a plane), line4 (0..3 form a line, no 6-plane), light (no 6-plane
and no 4-line). SAT = some matroid in the case has no deletable basis.

Usage: python hit10.py plane6|line4|light
"""
import itertools, sys, time
from pysat.solvers import Cadical195
from kum_r_n import build as _unused  # noqa: F401  (shared conventions)

N, r = 10, 4
var = lambda X, v: 5 * X + v
pc = lambda X: bin(X).count("1")
mask = lambda c: sum(1 << x for x in c)
case = sys.argv[1]
cls = []
low = {1: 1, 3: 2, 5: 3, 7: 4, 10: 4}
if case == "line4":
    low.update({7: 4})
if case in ("line4",):
    low[6 + 1] = 4
if case in ("line4", "light"):
    low[6] = 4          # no 6-plane
if case == "light":
    low[4] = 3          # no 4-line
for X in range(1 << N):
    for v in range(1, r):
        cls.append([-var(X, v + 1), var(X, v)])
    for v in range(pc(X) + 1, r + 1):
        cls.append([-var(X, v)])
    need = max([v for s, v in low.items() if pc(X) >= s], default=0)
    if need:
        cls.append([var(X, need)])
for X in range(1 << N):
    for a in range(N):
        if X >> a & 1:
            continue
        T = X | 1 << a
        for v in range(1, r + 1):
            cls.append([-var(X, v), var(T, v)])
            if v < r:
                cls.append([-var(T, v + 1), var(X, v)])
        for b in range(a + 1, N):
            if X >> b & 1:
                continue
            U, Xb = T | 1 << b, X | 1 << b
            for v in range(1, r + 1):
                c = [-var(U, v), var(T, v), var(Xb, v), var(X, v)]
                if v >= 2:
                    c.append(-var(X, v - 1))
                cls.append(c)
if case == "plane6":
    K = mask(range(6))
    cls += [[var(K, 3)], [-var(K, 4)]]
if case == "line4":
    L = mask(range(4))
    cls += [[var(L, 2)], [-var(L, 3)]]
for B in itertools.combinations(range(N), 4):
    rest = [x for x in range(N) if x not in B]
    c = [-var(mask(B), 4)]
    c += [-var(mask(Y), 2) for Y in itertools.combinations(rest, 2)]
    c += [-var(mask(Y), 3) for Y in itertools.combinations(rest, 4)]
    c += [-var(mask(Y), 4) for Y in itertools.combinations(rest, 5)]
    cls.append(c)
t = time.time()
s = Cadical195(bootstrap_with=cls)
res = s.solve()
print(f"hitting at k=2, case {case}: {'SAT (no deletable basis in some matroid)' if res else 'UNSAT (a deletable basis always exists)'} ({time.time() - t:.0f}s)")
if res:
    m = set(l for l in s.get_model() if l > 0)
    rk = lambda X: sum(1 for v in range(1, 5) if var(X, v) in m)
    fl = {}
    for j, nm in ((1, "points"), (2, "lines"), (3, "planes")):
        big = set()
        for size in range(2, 8):
            for c in itertools.combinations(range(N), size):
                if rk(mask(c)) == j:
                    F = frozenset(x for x in range(N) if rk(mask(c) | 1 << x) == j)
                    big.add(F)
        print(nm, sorted((len(F), sorted(F)) for F in big if len(F) >= j + 1)[-6:])
