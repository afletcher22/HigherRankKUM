"""Checks of the enumeration in slack_allmatroids.py.

 (1) Every relation of GL_4(F_2) and GL_4(F_3) (exhaustive) and of random matrices over F_5, F_7,
     F_11 must occur among the matroid relations.
 (2) The number of labelled sparse paving matroids in which W and W' are bases equals the number
     of independent sets of the Johnson graph J(8,4) avoiding W and W'; the two sides are counted
     independently (direct recursion against the enumerator, weighted by orbit sizes).

Usage: python slack_allmatroids_validate.py relations.npy
"""
import itertools, sys, time
import numpy as np
import slack_allmatroids as am
from slack_allmatroids_check import PAIRS, S4, pack, classes, member


def masks(A, q):
    m = np.zeros((len(A), 6, 6), dtype=np.int64)
    for i, (a, b) in enumerate(PAIRS):
        for j, (c, d) in enumerate(PAIRS):
            m[:, i, j] = (A[:, a, c] * A[:, b, d] - A[:, a, d] * A[:, b, c]) % q
    sg = [1, -1, 1, 1, -1, 1]
    det = sum(sg[j] * m[:, 0, j] * m[:, 5, 5 - j] for j in range(6)) % q
    return np.unique(pack((m[det != 0] != 0).astype(np.uint64)))


def main():
    t0 = time.time()
    cls, lab = classes(np.load(sys.argv[1]))
    print("classes %d, labelled %d" % (len(cls), len(lab)), flush=True)
    for q in (2, 3):
        got = []
        for lo in range(0, q ** 16, 1 << 20):
            idx = np.arange(lo, min(lo + (1 << 20), q ** 16), dtype=np.int64)
            got.append(masks(np.stack([(idx // q ** e) % q for e in range(16)], axis=1).reshape(-1, 4, 4), q))
        got = np.unique(np.concatenate(got))
        print("F_%d: %d relations, %d not among the matroid relations  [%.0fs]" % (
            q, len(got), (~member(got, lab)).sum(), time.time() - t0), flush=True)
    rng = np.random.default_rng(5)
    for q in (5, 7, 11):
        got = []
        for _ in range(6):
            A = rng.integers(0, q, size=(1 << 20, 4, 4)); A[rng.random(A.shape) < 0.45] = 0
            got.append(masks(A, q))
        got = np.unique(np.concatenate(got))
        print("F_%d sample: %d relations, %d not among the matroid relations  [%.0fs]" % (
            q, len(got), (~member(got, lab)).sum(), time.time() - t0), flush=True)

    # (2) independent sets of J(8,4) avoiding W and W'
    free = [s for s in am.SETS if s not in (am.WM, am.WP)]
    adj = [sum(1 << j for j, t in enumerate(free) if am.pc(s & t) == 3) for s in free]

    def count(cand):
        if not cand: return 1
        v = cand.bit_length() - 1
        rest = cand & ~(1 << v)
        return count(rest) + count(rest & ~adj[v])

    direct = count((1 << len(free)) - 1)
    ADJ = [(X, Y) for X in am.SETS for Y in am.SETS if X < Y and am.pc(X & Y) == 3]
    tot = {"sp": 0, "all": 0}; weight = [1]

    def leaf(lo, hi):
        cols = {X: am.val(am.var(X), lo, hi) for X in am.SETS}
        sp = np.ones(len(lo), dtype=bool)
        for X, Y in ADJ: sp &= cols[X] | cols[Y]
        tot["sp"] += weight[0] * int(sp.sum()); tot["all"] += weight[0] * len(lo)

    am.LEAF = leaf
    wts = (1 << np.arange(16)).reshape(4, 4)
    for g in am.g1_reps():
        M = ((g >> np.arange(16)) & 1).reshape(4, 4)
        weight[0] = len({int((M[list(p)][:, list(q)] * wts).sum()) for p in S4 for q in S4})
        am.run(np.array([g], dtype=np.uint64), np.zeros(1, dtype=np.uint64), 0)
    print("labelled matroids with W, W' bases: %d; sparse paving among them: %d; independent sets of J(8,4): %d  [%.0fs]" % (
        tot["all"], tot["sp"], direct, time.time() - t0))


if __name__ == "__main__":
    main()
