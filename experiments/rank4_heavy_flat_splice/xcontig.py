"""Contiguous insertion (McGuinness, Cyclic orderings of paving matroids, Proposition 13) in rank 4
for general matroids, as an exact SAT claim.

Claim XC(N): let S be a basis of a rank-4 matroid on N + 4 elements and e_0 .. e_{N-1} a cyclic
basis ordering of M - S. Then for some gap g and some order of S, inserting S as one block at gap g
gives a cyclic basis ordering of M.

Encoding: full rank function on all 2^(N+4) subsets (S = {0,1,2,3}, e_i = 4 + i), unit clauses
making S and every window of the e's a basis, and one clause per (gap, order of S) saying some
window of the merged sequence is not a basis. Options:
  simple   no parallel pairs;
  nopar    no element of S parallel to an element of E - S;
  gen      McGuinness local genericity everywhere: no s parallel to any e, no 3-circuit {s, s', e},
           no 3-circuit {s, e_i, e_j} with e_i, e_j within 3 consecutive positions;
  gaps=G   only the gaps in the comma list G (e.g. gaps=0,1 for two adjacent gaps);
  blocks2  also allow S in two blocks (sizes 1+3, 2+2, 3+1) at any two gaps.

Usage: python xcontig.py N [simple] [nopar] [gen] [gaps=...]
"""
import itertools, sys, time
from pysat.solvers import Cadical195

N = int(sys.argv[1])
opts = sys.argv[2:]
n, r = N + 4, 4
var = lambda X, v: 5 * X + v
pc = lambda X: bin(X).count("1")
mask = lambda c: sum(1 << x for x in c)
S = [0, 1, 2, 3]
E = [4 + i for i in range(N)]
gaps = next((list(map(int, a[5:].split(","))) for a in opts if a.startswith("gaps=")), range(N))

cls = []
for X in range(1 << n):
    for v in range(1, r):
        cls.append([-var(X, v + 1), var(X, v)])
    for v in range(pc(X) + 1, r + 1):
        cls.append([-var(X, v)])
    if pc(X) >= 1:
        cls.append([var(X, 1)])
    if "simple" in opts and pc(X) == 2:
        cls.append([var(X, 2)])
for X in range(1 << n):
    for a in range(n):
        if X >> a & 1:
            continue
        T = X | 1 << a
        for v in range(1, r + 1):
            cls.append([-var(X, v), var(T, v)])
            if v < r:
                cls.append([-var(T, v + 1), var(X, v)])
        for b in range(a + 1, n):
            if X >> b & 1:
                continue
            U, Xb = T | 1 << b, X | 1 << b
            for v in range(1, r + 1):
                c = [-var(U, v), var(T, v), var(Xb, v), var(X, v)]
                if v >= 2:
                    c.append(-var(X, v - 1))
                cls.append(c)
cls.append([var(mask(S), 4)])
for i in range(N):
    cls.append([var(mask(E[(i + t) % N] for t in range(4)), 4)])
if "nopar" in opts or "gen" in opts:
    for s in S:
        for e in E:
            cls.append([var(mask([s, e]), 2)])
if "gen" in opts:
    for s, s2 in itertools.combinations(S, 2):
        for e in E:
            cls.append([var(mask([s, s2, e]), 3)])
    for s in S:
        for i in range(N):
            for d in (1, 2):
                cls.append([var(mask([s, E[i], E[(i + d) % N]]), 3)])
def forbid(seq):
    L = len(seq)
    lits = []
    for j in range(L):
        W = [seq[(j + t) % L] for t in range(4)]
        if any(x < 4 for x in W):
            lits.append(-var(mask(W), 4))
    cls.append(lits)


for g in gaps:
    for perm in itertools.permutations(S):
        forbid(list(perm) + [E[(g + j) % N] for j in range(N)])   # S block before e_g
if "blocks2" in opts:
    # S in two blocks: the first a elements of an order of S before e_g, the rest before e_h
    for g in range(N):
        for d in range(1, N):
            for a in (1, 2, 3):
                for perm in itertools.permutations(S):
                    seq = []
                    for j in range(N):
                        if j == 0:
                            seq += list(perm[:a])
                        if j == d:
                            seq += list(perm[a:])
                        seq.append(E[(g + j) % N])
                    forbid(seq)

t = time.time()
s = Cadical195(bootstrap_with=cls)
res = s.solve()
print(f"XC({N}) {opts}: {'SAT (contiguous insertion can fail)' if res else 'UNSAT (holds)'} "
      f"({time.time() - t:.0f}s)", flush=True)
