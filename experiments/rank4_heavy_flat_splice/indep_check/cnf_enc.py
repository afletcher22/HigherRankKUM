"""Two independent CNF encodings of 'a rank-4 counterexample exists'.

E1 (exact): one Boolean ind[X] for every X of size 1..4 of the FULL ground set.
    ind[empty] = True implicitly.
    (hereditary)    ind[X+x] -> ind[X]
    (augmentation)  |I|=k, |J|=k+1 (k=1,2,3), J not a superset of I:
                    ind[I] & ind[J] -> OR_{x in J\\I} ind[I+x]
    A family of <=4-sets that is hereditary and satisfies augmentation for |J|=|I|+1 is
    exactly the independent-set family of a matroid of rank <= 4 (standard: the
    |J|=|I|+1 case implies the general case via a (|I|+1)-subset of J).  With S forced
    independent the rank is exactly 4.  So E1 models <-> rank-4 matroids on the ground
    set: NO relaxation.  basis(W) := ind[W] for |W|=4.

E2 (block relaxation): rank r(X) in {0..4}, order encoded (x[X,k] <-> r(X)>=k), only for
    X contained in some block B = S u {4 consecutive e's}.  On the Boolean lattice of each
    block impose r(0)=0, r(X)<=|X|, monotone, unit increase, and local submodularity
    r(X+a)+r(X+b) >= r(X+a+b)+r(X).  The restriction of any matroid to B satisfies these,
    so every genuine counterexample is a model (sound; UNSAT => claim holds).
    basis(W) := x[W,4].
"""
from itertools import combinations
from common import popcount


def bits(m):
    out = []
    while m:
        low = m & -m
        out.append(low)
        m ^= low
    return out


# ------------------------------------------------------------------------ E1

def exact_cnf(n, forced, clause_sets):
    var = {}
    by_size = {k: [] for k in range(1, 5)}
    nv = 0
    for k in range(1, 5):
        for c in combinations(range(n), k):
            m = 0
            for x in c:
                m |= 1 << x
            nv += 1
            var[m] = nv
            by_size[k].append(m)
    cls = []
    # hereditary
    for k in range(2, 5):
        for m in by_size[k]:
            vm = var[m]
            for b in bits(m):
                cls.append([-vm, var[m ^ b]])
    # augmentation, |I| = k, |J| = k+1
    n_aug = 0
    for k in range(1, 4):
        for I in by_size[k]:
            vI = var[I]
            for J in by_size[k + 1]:
                if I & J == I:
                    continue  # J superset of I: trivially satisfied
                c = [-vI, -var[J]]
                for b in bits(J & ~I):
                    c.append(var[I | b])
                cls.append(c)
                n_aug += 1
    for f in forced:
        cls.append([var[f]])
    for ws in clause_sets:
        cls.append([-var[w] for w in sorted(ws)])
    return var, cls, nv


# ------------------------------------------------------------------------ E2

def submasks(B):
    s = B
    while True:
        yield s
        if s == 0:
            return
        s = (s - 1) & B


def block_cnf(n, blocks, forced, clause_sets):
    subs = set()
    for B in blocks:
        subs.update(submasks(B))
    var = {}
    nv = 0
    for X in sorted(subs):
        for k in range(1, 5):
            nv += 1
            var[(X, k)] = nv
    cls = set()
    for X in subs:
        for k in range(1, 4):
            cls.add((-var[(X, k + 1)], var[(X, k)]))          # order encoding
        for k in range(popcount(X) + 1, 5):
            cls.add((-var[(X, k)],))                          # r(X) <= |X| (and r(0)=0)
    for B in blocks:
        for X in submasks(B):
            free = bits(B & ~X)
            for a in free:
                Xa = X | a
                for k in range(1, 5):
                    cls.add((-var[(X, k)], var[(Xa, k)]))     # monotone
                for k in range(1, 4):
                    cls.add((-var[(Xa, k + 1)], var[(X, k)]))  # r(X+a) <= r(X)+1
            for i in range(len(free)):
                for j in range(i + 1, len(free)):
                    a, b = free[i], free[j]
                    Xa, Xb, Xab = X | a, X | b, X | a | b
                    for k in range(0, 4):
                        c = [-var[(Xab, k + 1)], var[(Xa, k + 1)], var[(Xb, k + 1)]]
                        if k > 0:
                            c.append(-var[(X, k)])
                        cls.add(tuple(c))
    cls = [list(c) for c in cls]
    for f in forced:
        cls.append([var[(f, 4)]])
    for ws in clause_sets:
        cls.append([-var[(w, 4)] for w in sorted(ws)])
    return var, cls, nv
