"""Chains of three bases (rank 5, F_2) in which every consecutive pair of bases is totally tight,
i.e. no admissible choice (x_i, x_{i+1}) gives a slack pair-split relation.

Needs pairsplit_pairs_totally_tight.npy (written by pairsplit_pairs.py).  B_0 = unit vectors,
B_1 = columns of A, B_2 = columns of A C, with A, C and (A C)^-1 all totally tight; A runs over
representatives up to permuting B_0 and B_1, C over all totally tight matrices.

For every such chain the script computes  margin = min over proper nonzero subspaces F of
3 dim(F) - |F|  (> 0 strict, = 0 tight flat, < 0 not uniformly dense).

Usage: python pairsplit_triples.py
"""
import itertools, time
from collections import Counter
import numpy as np
from pairsplit_tightsearch import margin

R = 5
SH = np.arange(25, dtype=np.uint32).reshape(5, 5)


def to_mat(codes):
    codes = np.asarray(codes, dtype=np.uint32)
    return ((codes[:, None, None] >> SH) & 1).astype(np.uint8)


def to_code(mats):
    return (mats.astype(np.uint32) << SH).sum(axis=(1, 2), dtype=np.uint32)


def inverse(M):
    M = [[int(v) for v in row] + [int(i == j) for j in range(R)] for i, row in enumerate(M)]
    for c in range(R):
        p = next(r for r in range(c, R) if M[r][c]); M[c], M[p] = M[p], M[c]
        for r in range(R):
            if r != c and M[r][c]: M[r] = [a ^ b for a, b in zip(M[r], M[c])]
    return [row[R:] for row in M]


def main():
    t0 = time.time()
    tt = np.load("pairsplit_pairs_totally_tight.npy")
    mats = to_mat(tt)
    ttset = set(tt.tolist())
    inv_codes = to_code(np.array([inverse(m) for m in mats], dtype=np.uint8))
    print("totally tight matrices: %d  [%.0fs]" % (len(tt), time.time() - t0), flush=True)
    # representatives up to row and column permutations
    perms = list(itertools.permutations(range(R)))
    seen = set(); reps = []
    for code, m in zip(tt.tolist(), mats):
        if code in seen: continue
        reps.append(m)
        for p in perms:
            seen.update(to_code(np.stack([m[list(p)][:, list(q)] for q in perms])).tolist())
    print("classes up to relabelling the two bases: %d  [%.0fs]" % (len(reps), time.time() - t0), flush=True)
    from pairsplit_tightsearch import SUBS
    member = np.zeros((len(SUBS), 32), dtype=np.int32)
    for i, (vs, d) in enumerate(SUBS): member[i, vs] = 1
    dims = np.array([d for _, d in SUBS], dtype=np.int32)
    w = (1 << np.arange(R, dtype=np.int32))
    hist = Counter(); best = None; total = 0
    for A in reps:
        AC = (np.einsum("ij,njk->nik", A.astype(np.int32), mats.astype(np.int32)) & 1).astype(np.uint8)
        hit = np.isin(to_code(AC), inv_codes)
        AC = AC[hit]; total += len(AC)
        if not len(AC): continue
        cnt = np.zeros((len(AC), 32), dtype=np.int32)
        fixed = [1 << r for r in range(R)] + [int((A[:, c] * w).sum()) for c in range(R)]
        for v in fixed: cnt[:, v] += 1
        cols2 = (AC.astype(np.int32) * w[None, :, None]).sum(axis=1)          # (n, 5) column codes
        for c in range(R): np.add.at(cnt, (np.arange(len(AC)), cols2[:, c]), 1)
        marg = (3 * dims[None, :] - cnt @ member.T).min(axis=1)
        for m, c in zip(*np.unique(marg, return_counts=True)): hist[int(m)] += int(c)
        i = int(marg.argmax())
        if best is None or marg[i] > best[0]: best = (int(marg[i]), fixed + cols2[i].tolist())
    print("chains with all three pairs totally tight (A up to relabelling): %d  [%.0fs]" % (total, time.time() - t0))
    print("margin histogram (>0 strict, 0 tight flat, <0 not uniformly dense):", dict(sorted(hist.items())))
    if best: print("largest margin %d: %s" % (best[0], [format(v, "05b") for v in best[1]]))


if __name__ == "__main__":
    main()
