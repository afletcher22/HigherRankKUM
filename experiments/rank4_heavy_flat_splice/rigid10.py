"""Rigid 5-pair chains on 10 elements (rank 4), in cyclic coordinates.

Following the dependent matchings D_i of a rigid chain P_0..P_4 visits all ten elements in one cycle
z_0..z_9 with z_j in P_{2j}. In these coordinates (elements = Z_10) a rigid chain is exactly:

* bases m + {0,3,5,8}  (the chain windows P_i + P_{i+1}; P_{2m} = {m, m+5}, P_{2m+1} = {m+3, m+8});
* bases j + {0,3,6,8}  (the entries of the relations R_i);
* rank 3 for j + {0,1,3,8} (the non-entries).

This script computes the backbone (4-sets forced to be bases or dependent) and the cyclic orders
all of whose windows are forced bases.

Usage: python rigid10.py [backbone] [orders]
"""
import itertools, sys
from pysat.solvers import Cadical195

N, r = 10, 4
var = lambda X, v: 5 * X + v
pc = lambda X: bin(X).count("1")
mask = lambda c: sum(1 << (x % N) for x in c)


def base_clauses():
    cls = []
    for X in range(1 << N):
        for v in range(1, r):
            cls.append([-var(X, v + 1), var(X, v)])
        for v in range(pc(X) + 1, r + 1):
            cls.append([-var(X, v)])
        if pc(X) >= 1:
            cls.append([var(X, 1)])
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
    cls.append([var((1 << N) - 1, 4)])
    for j in range(N):
        cls.append([var(mask([j, j + 3, j + 5, j + 8]), 4)])
        cls.append([var(mask([j, j + 3, j + 6, j + 8]), 4)])
        cls.append([-var(mask([j, j + 1, j + 3, j + 8]), 4)])
    return cls


if __name__ == "__main__":
    cls = base_clauses()
    s = Cadical195(bootstrap_with=cls)
    assert s.solve(), "rigid chains exist"
    quads = list(itertools.combinations(range(N), 4))
    forced_b, forced_d, free = [], [], []
    for q in quads:
        B = var(mask(q), 4)
        can_dep = s.solve(assumptions=[-B])
        can_base = s.solve(assumptions=[B])
        (forced_b if not can_dep else forced_d if not can_base else free).append(q)
    print("forced bases:", len(forced_b), "forced dependent:", len(forced_d), "free:", len(free))
    print("forced dependent:", forced_d)
    print("free:", free)
    if "orders" in sys.argv:
        fb = set(mask(q) for q in forced_b)
        good = []
        for rest in itertools.permutations(range(1, N)):
            if rest[0] > rest[-1]:
                continue
            seq = (0,) + rest
            if all(mask([seq[(i + t) % N] for t in range(4)]) in fb for i in range(N)):
                good.append(seq)
        print("cyclic orders whose windows are all forced bases:", len(good))
        for g in good[:20]:
            print(" ", g)
