"""Blocked pairs of matrices over F_q (q = 2 or 3, exhaustive), and the reductions used in Section 9
of docs/research-ledger/BEYOND_RANK4_ROUTES.md.

A1, A2 in GL_4(F_q) (rows W, columns W') are *blocked* if no pair (P, P') of 2-sets has
det A1[P, P'] != 0 and det A2[P, P'] != 0.  The script reports

  * the relations (supports of the 2 x 2 minors), how many are tight, and whether every tight
    relation contains a bijection;
  * for every blocked pair, whether a member is slack or contains no bijection;
  * the blocked pairs in which both matrices have total support (every nonzero entry lies on a
    nonzero transversal), by support pattern up to A1 -> P A1 Q, A2 -> P A2 Q;
  * with the argument `star n`: a test on n random pairs of the rank criterion
        blocked  iff  for every P: rank A2[P, supp_1 P] <= 1 or rank A1[P, supp_2 P] <= 1,
    where supp_k P is the set of columns in which the rows P of A_k are not both zero.

Usage: python slack_blocked.py q            (q = 2, 3)
       python slack_blocked.py q star n     (any prime q)
"""
import itertools, sys, time
import numpy as np
from collections import Counter

PAIRS = list(itertools.combinations(range(4), 2)); PI = {p: i for i, p in enumerate(PAIRS)}
S4 = list(itertools.permutations(range(4)))
IND = [[PI[tuple(sorted((p[a], p[b])))] for (a, b) in PAIRS] for p in S4]
W36 = (1 << np.arange(36, dtype=np.uint64)).reshape(6, 6)
BIJ = np.array([sum(1 << (6 * i + IND[k][i]) for i in range(6)) for k in range(24)], dtype=np.uint64)


def total_support_table():
    pat = np.arange(1 << 16)
    P = ((pat[:, None] >> np.arange(16)) & 1).reshape(-1, 4, 4).astype(bool)
    cover = np.zeros_like(P)
    for p in S4:
        t = np.ones(len(P), dtype=bool)
        for i in range(4): t &= P[:, i, p[i]]
        for i in range(4): cover[:, i, p[i]] |= t
    return (cover == P).all(axis=(1, 2)) & P.any(axis=(1, 2))


def collect(q):
    """Distinct relations over GL_4(F_q), and distinct (relation, support pattern) over the
    matrices of total support."""
    TS = total_support_table(); rels = set(); keys = set()
    for lo in range(0, q ** 16, 1 << 20):
        idx = np.arange(lo, min(lo + (1 << 20), q ** 16), dtype=np.int64)
        A = np.stack([(idx // q ** e) % q for e in range(16)], axis=1)
        sp = ((A != 0) << np.arange(16)).sum(axis=1)
        A = A.reshape(-1, 4, 4)
        m = np.zeros((len(A), 6, 6), dtype=np.int64)
        for i, (a, b) in enumerate(PAIRS):
            for j, (c, d) in enumerate(PAIRS):
                m[:, i, j] = (A[:, a, c] * A[:, b, d] - A[:, a, d] * A[:, b, c]) % q
        sg = [1, -1, 1, 1, -1, 1]
        ok = sum(sg[j] * m[:, 0, j] * m[:, 5, 5 - j] for j in range(6)) % q != 0
        mask = ((m[ok] != 0).astype(np.uint64) * W36).sum(axis=(1, 2)).astype(np.uint64)
        rels.update(np.unique(mask).tolist())
        t = TS[sp[ok]]
        keys.update(map(tuple, np.unique(np.stack([mask[t], sp[ok][t].astype(np.uint64)], axis=1), axis=0).tolist()))
    return np.array(sorted(rels), dtype=np.uint64), np.array(sorted(keys), dtype=np.uint64)


def canon_pair(sa, sb):
    a = np.array([(sa >> k) & 1 for k in range(16)]).reshape(4, 4)
    b = np.array([(sb >> k) & 1 for k in range(16)]).reshape(4, 4)
    return min(min((tuple(x[list(p)][:, list(r)].reshape(16)), tuple(y[list(p)][:, list(r)].reshape(16)))
                   for p in S4 for r in S4) for x, y in ((a, b), (b, a)))


def exhaustive(q):
    t0 = time.time()
    um, K = collect(q); mask, sp = K[:, 0], K[:, 1].astype(np.int64)
    hit = um[:, None] & BIJ[None, :]
    tight = (hit == 0).any(axis=1); cont = (hit == BIJ[None, :]).any(axis=1)
    print("F_%d: %d relations, %d tight; tight relations containing no bijection: %d  [%.0fs]" % (
        q, len(um), tight.sum(), (tight & ~cont).sum(), time.time() - t0), flush=True)
    c = Counter(); pats = Counter()
    for i in range(len(um)):
        k = int(((um[i] & um) == 0).sum())
        c["blocked pairs of relations"] += k
        c["... with a slack member"] += 0 if tight[i] else k
        c["... with a member containing no bijection"] += 0 if cont[i] else k
    for i in range(len(K)):
        blk = (mask[i] & mask) == 0
        c["blocked pairs, both of total support"] += int(blk.sum())
        for s in set(sp[blk].tolist()): pats[canon_pair(int(sp[i]), s)] += 1
    for k, v in c.items(): print("  %-45s %d" % (k, v))
    print("support patterns of the blocked pairs of total support, up to symmetry: %d  [%.0fs]" % (len(pats), time.time() - t0))
    fmt = lambda x: " ".join("".join(map(str, x[4 * i:4 * i + 4])) for i in range(4))
    for (x, y), _ in sorted(pats.items(), key=lambda t: (sum(t[0][0]) + sum(t[0][1]), t[0])):
        print("  A1: %s   A2: %s" % (fmt(x), fmt(y)))


def star_test(q, n, seed=1):
    rng = np.random.default_rng(seed)

    def minors(A):
        return np.array([[(A[a, c] * A[b, d] - A[a, d] * A[b, c]) % q for (c, d) in PAIRS] for (a, b) in PAIRS])

    def det(A):
        m = minors(A); sg = [1, -1, 1, 1, -1, 1]
        return sum(sg[j] * m[0, j] * m[5, 5 - j] for j in range(6)) % q

    def rank_le1(R):
        k = R.shape[1]
        return all((R[0, c] * R[1, d] - R[0, d] * R[1, c]) % q == 0 for c in range(k) for d in range(c + 1, k))

    def star(A1, A2):
        for P in PAIRS:
            s1 = [c for c in range(4) if A1[P[0], c] or A1[P[1], c]]
            s2 = [c for c in range(4) if A2[P[0], c] or A2[P[1], c]]
            if not (rank_le1(A2[list(P)][:, s1]) or rank_le1(A1[list(P)][:, s2])): return False
        return True

    def rand():
        while True:
            A = rng.integers(0, q, size=(4, 4)); A[rng.random((4, 4)) < 0.55] = 0
            if det(A): return A

    blocked = bad = 0
    for _ in range(n):
        A1, A2 = rand(), rand()
        b = not ((minors(A1) != 0) & (minors(A2) != 0)).any()
        blocked += b; bad += (b != star(A1, A2))
    print("F_%d: %d pairs, %d blocked, rank criterion disagrees on %d" % (q, n, blocked, bad))


if __name__ == "__main__":
    q = int(sys.argv[1])
    if len(sys.argv) > 2 and sys.argv[2] == "star": star_test(q, int(sys.argv[3]))
    else: exhaustive(q)
