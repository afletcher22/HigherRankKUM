"""The slack lemma on the level-2 relations of all rank-4 matroids on W + W' (output of
slack_allmatroids.py).

Two matroids M1, M2 on W + W' (W, W' bases of both) are *blocked* if they have no common basis
meeting W in two elements, i.e. their relations are disjoint.  (A 2-cycle of pair-split relations
in matroids N, N' fails to close iff N and the dual of N' are blocked.)  A relation is *tight* if
it is blocked against the relation of a bijection pi : W -> W' (no (W - P) + pi(P) is a basis),
*slack* otherwise, and it *contains* pi if every (W - P) + pi(P) is a basis.

Checked here:
  (S)  in every blocked pair both relations contain a bijection (so both are tight);
  with the argument `closure`: every product a . b of two relations is again a relation, so (S)
  extends to cycles of any length.

Usage: python slack_allmatroids_check.py relations.npy [closure]
"""
import itertools, sys, time
import numpy as np
from collections import Counter

PAIRS = list(itertools.combinations(range(4), 2)); PI = {p: i for i, p in enumerate(PAIRS)}
S4 = list(itertools.permutations(range(4)))
IND = np.array([[PI[tuple(sorted((p[a], p[b])))] for (a, b) in PAIRS] for p in S4])
W36 = (np.uint64(1) << np.arange(36, dtype=np.uint64)).reshape(6, 6)
BIJ = np.array([sum(1 << (6 * i + IND[k][i]) for i in range(6)) for k in range(24)], dtype=np.uint64)


def unpack(x):
    return ((x[:, None] >> np.arange(36, dtype=np.uint64)) & np.uint64(1)).reshape(-1, 6, 6).astype(np.uint64)


def pack(b):
    return (b * W36).sum(axis=(1, 2)).astype(np.uint64)


def images(x):
    """All 576 relabellings of each relation, shape (576, n)."""
    b = unpack(x); out = []
    for p in range(24):
        bp = b[:, np.argsort(IND[p])]
        for q in range(24): out.append(pack(bp[:, :, np.argsort(IND[q])]))
    return np.stack(out)


def classes(rel):
    canon = np.concatenate([images(rel[s:s + 20000]).min(axis=0) for s in range(0, len(rel), 20000)])
    cls = np.unique(canon)
    lab = np.unique(np.concatenate([np.unique(images(cls[s:s + 20000])) for s in range(0, len(cls), 20000)]))
    return cls, lab


def member(x, lab):
    i = np.minimum(np.searchsorted(lab, x), len(lab) - 1)
    return lab[i] == x


def main():
    t0 = time.time()
    rel = np.load(sys.argv[1])
    cls, lab = classes(rel)
    print("relations found: %d; classes up to S4 x S4: %d; labelled relations: %d  [%.0fs]" % (
        len(rel), len(cls), len(lab), time.time() - t0), flush=True)
    hit = cls[:, None] & BIJ[None, :]
    tight = (hit == 0).any(axis=1); cont = (hit == BIJ[None, :]).any(axis=1)
    print("tight classes: %d, slack: %d; classes containing a bijection: %d; tight classes containing none: %d" % (
        tight.sum(), (~tight).sum(), cont.sum(), (tight & ~cont).sum()), flush=True)
    labcont = ((lab[:, None] & BIJ[None, :]) == BIJ[None, :]).any(axis=1)
    c = Counter(); blocked = np.zeros(len(cls), dtype=bool)
    for i, a in enumerate(cls):
        blk = (a & lab) == 0
        k = int(blk.sum())
        if not k: continue
        blocked[i] = True
        c["blocked pairs (class of M1, labelled M2)"] += k
        c["... with M1 slack"] += 0 if tight[i] else k
        c["... with M1 containing no bijection"] += 0 if cont[i] else k
        c["... with M2 containing no bijection"] += int((~labcont[blk]).sum())
    for k, v in c.items(): print("  %-45s %d" % (k, v))
    print("classes blocked against something: %d (tight classes: %d)  [%.0fs]" % (
        blocked.sum(), tight.sum(), time.time() - t0), flush=True)
    if len(sys.argv) > 2 and sys.argv[2] == "closure":
        # products a . sigma . b over class representatives a, b and relabellings sigma of the middle block
        mids = np.unique(np.concatenate([pack(unpack(cls)[:, np.argsort(IND[p])]) for p in range(24)]))
        mrows = [(mids >> np.uint64(6 * i)) & np.uint64(63) for i in range(6)]
        total = new = 0
        for a in cls.tolist():
            prod = np.zeros(len(mids), dtype=np.uint64)
            for i in range(6):
                r = np.zeros(len(mids), dtype=np.uint64)
                for j in range(6):
                    if a >> (6 * i + j) & 1: r |= mrows[j]
                prod |= r << np.uint64(6 * i)
            prod = np.unique(prod); total += len(prod)
            new += int((~member(prod, lab)).sum())
        print("products a.sigma.b: %d (distinct for fixed a), not among the matroid relations: %d  [%.0fs]" % (
            total, new, time.time() - t0))


if __name__ == "__main__":
    main()
