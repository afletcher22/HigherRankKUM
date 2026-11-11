"""Search for chains of three bases (rank 5, F_2) with a valid root split whose pair split does
not close, and measure how far the resulting 15-element matroid is from strict density.

x_0 = e0 and W_0 = {e1, ..., e4}.  The next blocks are built from the contraction matrices:
    W_1 = S_0 W_0 + u x_1,      W_2 = S_1 W_1 + u' x_2
so that modulo x_1 (resp. x_2) the block W_1 (resp. W_2) has matrix S_0 (resp. S_1) in the
previous block.  S_0 and S_1 are drawn from the *tight* matrices of GL_4(2) (mode `tight`) or are
the identity (mode `rigid`, exhaustive over x_1, x_2, u, u').

For every failing chain the script prints  margin = min over proper nonzero subspaces F of
3 dim(F) - |F|:  margin > 0 strict, margin = 0 uniformly dense with a tight flat, margin < 0 not
uniformly dense.

Usage: python pairsplit_tightsearch.py rigid
       python pairsplit_tightsearch.py tight n_samples seed
"""
import itertools, random, sys, time
from collections import Counter
import numpy as np
from pairsplit_local import PAIRS, IND, relation, det4

E = [1 << i for i in range(5)]


def rank(vs):
    basis = []
    for v in vs:
        for b in basis:
            v = min(v, v ^ b)
        if v: basis.append(v)
    return len(basis)


def subspaces():
    seen = {}
    for t in range(1, 5):
        for gens in itertools.combinations(range(1, 32), t):
            span = {0}
            for g in gens: span |= {s ^ g for s in span}
            if len(span) == 1 << t: seen[frozenset(span)] = t
    return [(sorted(s - {0}), d) for s, d in seen.items()]


SUBS = subspaces()


def margin(vecs):
    cnt = Counter(vecs)
    return min(3 * d - sum(cnt[v] for v in s) for s, d in SUBS)


def rel(W, x, Wn):
    """T(Q, Q') = [Q + x + (Wn - Q') independent], as a 6 x 6 boolean matrix."""
    T = np.zeros((6, 6), dtype=bool)
    for a, Q in enumerate(PAIRS):
        q = [W[Q[0]], W[Q[1]], x]
        if rank(q) < 3: continue
        for b, Qp in enumerate(PAIRS):
            T[a, b] = rank(q + [Wn[i] for i in range(4) if i not in Qp]) == 5
    return T


def bmul(A, B):
    return (A.astype(np.uint8) @ B.astype(np.uint8)) > 0


def study(x, W):
    """x = [x0, x1, x2], W = [W0, W1, W2].  None if not a chain with a valid root split, else
    (pair split closes, relations)."""
    for i in range(3):
        if rank([x[i]] + W[i]) < 5 or rank(W[i] + [x[(i + 1) % 3]]) < 5: return None
    Ts = [rel(W[i], x[(i + 1) % 3], W[(i + 1) % 3]) for i in range(3)]
    return bool(bmul(bmul(Ts[0], Ts[1]), Ts[2]).diagonal().any()), Ts


def build(S0, u, x1, S1, up, x2):
    W0 = E[1:]
    W1 = [(x1 if u[j] else 0) ^ sum_xor(W0[l] for l in range(4) if S0[l][j]) for j in range(4)]
    W2 = [(x2 if up[j] else 0) ^ sum_xor(W1[l] for l in range(4) if S1[l][j]) for j in range(4)]
    return [E[0], x1, x2], [W0, W1, W2]


def sum_xor(it):
    r = 0
    for v in it: r ^= v
    return r


def tight_matrices():
    out = []
    for v in itertools.product(range(2), repeat=16):
        A = [list(v[4 * i:4 * i + 4]) for i in range(4)]
        if not det4(A, 2): continue
        rows = relation(A, 2)
        if not all(any(rows[i] >> int(IND[p][i]) & 1 for i in range(6)) for p in range(24)):
            out.append(A)
    return out


def report(fails, tested, t0):
    hist = Counter(m for m, _ in fails)
    print("chains with a valid root split: %d; pair split fails: %d  [%.0fs]" % (tested, len(fails), time.time() - t0))
    print("margin histogram of the failures (>0 strict, 0 tight flat, <0 not uniformly dense):",
          dict(sorted(hist.items())))
    best = max(fails, key=lambda f: f[0], default=None)
    if best:
        m, (x, W) = best
        print("largest margin %d:  x = %s  W = %s" % (m, [format(v, "05b") for v in x],
                                                      [[format(v, "05b") for v in w] for w in W]))


def main():
    t0 = time.time(); fails = []; tested = 0
    I4 = [[int(i == j) for j in range(4)] for i in range(4)]
    if sys.argv[1] == "rigid":
        for x1 in range(1, 32):
            if not x1 & 1: continue          # W_0 + x_1 a basis
            for x2 in range(1, 32):
                for u in itertools.product(range(2), repeat=4):
                    for up in itertools.product(range(2), repeat=4):
                        x, W = build(I4, u, x1, I4, up, x2)
                        res = study(x, W)
                        if res is None: continue
                        tested += 1
                        if not res[0]: fails.append((margin(x + W[0] + W[1] + W[2]), (x, W)))
    else:
        n, rng = int(sys.argv[2]), random.Random(int(sys.argv[3]))
        tm = tight_matrices()
        print("tight matrices in GL_4(2): %d of 20160" % len(tm), flush=True)
        for it in range(n):
            S0, S1 = rng.choice(tm), rng.choice(tm)
            u = [rng.randrange(2) for _ in range(4)]; up = [rng.randrange(2) for _ in range(4)]
            x1 = rng.randrange(1, 32) | 1; x2 = rng.randrange(1, 32)
            x, W = build(S0, u, x1, S1, up, x2)
            res = study(x, W)
            if res is None: continue
            tested += 1
            if not res[0]: fails.append((margin(x + W[0] + W[1] + W[2]), (x, W)))
            if (it + 1) % 100000 == 0: report(fails, tested, t0); sys.stdout.flush()
    report(fails, tested, t0)


if __name__ == "__main__":
    main()
