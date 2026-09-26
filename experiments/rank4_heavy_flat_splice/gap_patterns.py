"""Failure patterns of contiguous insertion at one gap, rank 4 (McGuinness S-pairs, general
matroids).

Local picture: S = {0,1,2,3} a basis; x3 x2 x1 | y1 y2 y3 six consecutive elements of a cyclic
basis ordering of M - S (elements 4..9 = x3 x2 x1 y1 y2 y3), so {x3,x2,x1,y1}, {x2,x1,y1,y2},
{x1,y1,y2,y3} are bases. Inserting S in order p1 p2 p3 p4 at the gap creates the windows
  {x1, p1, p2, p3}, {x2, x1, p1, p2}, {x3, x2, x1, p1}   (prefixes A of the order: A + X_{4-|A|})
  {p2, p3, p4, y1}, {p3, p4, y1, y2}, {p4, y1, y2, y3}   (suffixes A: A + Y_{4-|A|}).
H1 = {A : A + X_{4-|A|} dependent}, H2 = {A : A + Y_{4-|A|} dependent}, for 1 <= |A| <= 3.
The gap fails if every order has a prefix in H1 or a suffix in H2.

This script enumerates the realizable failing pairs (H1, H2) up to permutations of S (and the
reflection swapping the two sides), with the "defect" data: which small sets are dependent.

Usage: python gap_patterns.py [paving|simple]
"""
import itertools, sys
from pysat.solvers import Cadical195

opts = sys.argv[1:]
n, r = 10, 4
var = lambda X, v: 5 * X + v
pc = lambda X: bin(X).count("1")
mask = lambda c: sum(1 << x for x in c)
S = [0, 1, 2, 3]
x3, x2, x1, y1, y2, y3 = 4, 5, 6, 7, 8, 9
X = [x1, x2, x3]          # X_i = first i of these (nearest the gap first)
Y = [y1, y2, y3]

cls = []
for Z in range(1 << n):
    for v in range(1, r):
        cls.append([-var(Z, v + 1), var(Z, v)])
    for v in range(pc(Z) + 1, r + 1):
        cls.append([-var(Z, v)])
    if pc(Z) >= 1:
        cls.append([var(Z, 1)])
    if "simple" in opts and pc(Z) == 2:
        cls.append([var(Z, 2)])
    if "paving" in opts and 1 <= pc(Z) <= 3:
        cls.append([var(Z, pc(Z))])
for Z in range(1 << n):
    for a in range(n):
        if Z >> a & 1:
            continue
        T = Z | 1 << a
        for v in range(1, r + 1):
            cls.append([-var(Z, v), var(T, v)])
            if v < r:
                cls.append([-var(T, v + 1), var(Z, v)])
        for b in range(a + 1, n):
            if Z >> b & 1:
                continue
            U, Zb = T | 1 << b, Z | 1 << b
            for v in range(1, r + 1):
                c = [-var(U, v), var(T, v), var(Zb, v), var(Z, v)]
                if v >= 2:
                    c.append(-var(Z, v - 1))
                cls.append(c)
cls.append([var(mask(S), 4)])
for W in ([x3, x2, x1, y1], [x2, x1, y1, y2], [x1, y1, y2, y3]):
    cls.append([var(mask(W), 4)])

subsets = [A for k in (1, 2, 3) for A in itertools.combinations(S, k)]
h1 = {A: -var(mask(list(A) + X[:4 - len(A)]), 4) for A in subsets}     # literal: A in H1
h2 = {A: -var(mask(list(A) + Y[:4 - len(A)]), 4) for A in subsets}
for perm in itertools.permutations(S):
    pre = [tuple(sorted(perm[:k])) for k in (1, 2, 3)]
    suf = [tuple(sorted(perm[4 - k:])) for k in (1, 2, 3)]
    cls.append([h1[A] for A in pre] + [h2[A] for A in suf])

s = Cadical195(bootstrap_with=cls)
fmt = lambda fam: "{" + ", ".join("".join("abcd"[x] for x in A) for A in fam) + "}"


def canon(H1, H2):
    best = None
    for p in itertools.permutations(range(4)):
        for side in (0, 1):
            a, b = (H1, H2) if side == 0 else (H2, H1)
            key = (tuple(sorted(tuple(sorted(p[x] for x in A)) for A in a)),
                   tuple(sorted(tuple(sorted(p[x] for x in A)) for A in b)))
            key = (tuple(sorted(key[0], key=lambda t: (len(t), t))),
                   tuple(sorted(key[1], key=lambda t: (len(t), t))))
            if best is None or key < best:
                best = key
    return best


seen = {}
while s.solve():
    model = set(l for l in s.get_model() if l > 0)
    isdep = lambda lit: (-lit) not in model        # lit = -var(W,4): true iff W is dependent
    H1 = [A for A in subsets if isdep(h1[A])]
    H2 = [A for A in subsets if isdep(h2[A])]
    key = canon(H1, H2)
    seen[key] = (H1, H2)
    # block this exact (H1, H2)
    s.add_clause([(-h1[A] if A in H1 else h1[A]) for A in subsets] +
                 [(-h2[A] if A in H2 else h2[A]) for A in subsets])
print(f"{opts}: {len(seen)} failing patterns up to symmetry")
by_size = sorted(seen.items(), key=lambda kv: (len(kv[0][0]) + len(kv[0][1]), kv[0]))
minimal = [k for k, _ in by_size
           if not any(o != k and set(o[0]) <= set(k[0]) and set(o[1]) <= set(k[1]) for o in seen)]
print(f"inclusion-minimal patterns: {len(minimal)}")
for k in minimal:
    print("  H1 =", fmt(k[0]), " H2 =", fmt(k[1]))
