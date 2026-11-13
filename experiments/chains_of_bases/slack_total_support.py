"""Blocked pairs of matroids of total support, over all matroids of rank 4 on W + W'.

A matroid (W, W' bases) has *total support* if every edge of its exchange graph between W and W'
(W - a + b a basis) lies in a perfect matching of that graph; it is then the direct sum of its
restrictions to the components of the graph.  For matrices this is the case that the
degeneration of Section 9 of the research note reduces to.

Lists, by the pair of exchange graphs up to relabelling W and W', all blocked pairs (no common
basis meeting W in two elements) in which both matroids have total support.

Usage: python slack_total_support.py
"""
import itertools, time
import numpy as np
from collections import Counter
import slack_allmatroids as am
from slack_allmatroids_check import BIJ, images
from slack_blocked import total_support_table, canon_pair, S4

t0 = time.time()
TS = total_support_table()
got = {}
def leaf(lo, hi):
    for t in np.unique(lo >> np.uint64(16)).tolist(): got.setdefault(t, cur[0])
am.LEAF = leaf
cur = [0]
for g in am.g1_reps():
    if not TS[g]: continue
    cur[0] = g
    am.run(np.array([g], dtype=np.uint64), np.zeros(1, dtype=np.uint64), 0)
rel = np.array(sorted(got), dtype=np.uint64); g1 = np.array([got[int(t)] for t in rel])
print("matroids of total support (exchange graph up to symmetry): %d relations  [%.0fs]" % (len(rel), time.time() - t0), flush=True)
# all relabellings of these relations, with the relabelled exchange graph
wts = (1 << np.arange(16)).reshape(4, 4)
lab = {}
for s in range(0, len(rel), 5000):
    im = images(rel[s:s + 5000]); k = 0
    for p in S4:
        for q in S4:
            for t, g in zip(im[k].tolist(), g1[s:s + 5000].tolist()):
                if t not in lab:
                    M = ((g >> np.arange(16)) & 1).reshape(4, 4)
                    X = np.zeros((4, 4), dtype=np.int64); X[np.ix_(list(p), list(q))] = M
                    lab[t] = int((X * wts).sum())
            k += 1
L = np.array(sorted(lab), dtype=np.uint64); LG = np.array([lab[int(t)] for t in L])
cont = ((L[:, None] & BIJ[None, :]) == BIJ[None, :]).any(axis=1)
print("labelled relations of total support: %d  [%.0fs]" % (len(L), time.time() - t0), flush=True)
pats = Counter(); n = bad = 0
for i, a in enumerate(rel.tolist()):
    blk = (np.uint64(a) & L) == 0
    n += int(blk.sum()); bad += int((~cont[blk]).sum())
    for g in set(LG[blk].tolist()): pats[canon_pair(int(g1[i]), int(g))] += 1
print("blocked pairs of total support: %d; with a member containing no bijection: %d; pairs of exchange graphs up to symmetry: %d  [%.0fs]" % (
    n, bad, len(pats), time.time() - t0))
fmt = lambda x: " ".join("".join(map(str, x[4 * i:4 * i + 4])) for i in range(4))
for (x, y), _ in sorted(pats.items(), key=lambda t: (sum(t[0][0]) + sum(t[0][1]), t[0])):
    print("  M1: %s   M2: %s" % (fmt(x), fmt(y)))
