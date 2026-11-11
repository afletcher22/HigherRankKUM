"""Pair-split relations from several fields at once: F_2 and F_3 exhaustively, F_5 and F_7 by
6,000,000 sampled matrices each.  Checks that the union of the relation types is closed under
composition, that no slack type occurs in a cycle that does not close, and counts the types that
contain a bijection.  Takes a few minutes; caches the generators in the given directory.

Usage: python pairsplit_union.py cache_dir
"""
import sys, os, random, time
import numpy as np
from pairsplit_local import *
SP = sys.argv[1]
t0 = time.time()
def gens_for(q, sample=0):
    f = os.path.join(SP, "gens%d_%d.npy" % (q, sample))
    if os.path.exists(f): return np.load(f)
    g = np.unique(canon(generators(q, sample, random.Random(q))))
    np.save(f, g); return g
G = {q: gens_for(q) for q in (2, 3)}
G[5] = gens_for(5, 6_000_000)
G[7] = gens_for(7, 6_000_000)
for q in G: print("F_%d: %d classes" % (q, len(G[q])))
gens = np.unique(np.concatenate(list(G.values())))
print("union: %d classes  [%.0fs]" % (len(gens), time.time() - t0), flush=True)
grow = unpack(gens)
pi = meets(grow, IND)
pi_cnt = pi.sum(axis=1)
# contained bijections
def contains(rows, perms):
    out = np.ones((len(rows), len(perms)), dtype=bool)
    for i in range(6):
        out &= (rows[:, i][:, None] >> perms[:, i][None, :].astype(np.uint8) & 1).astype(bool)
    return out
C = contains(grow, IND).sum(axis=1)
print("tight classes (Pi < 24): %d;  classes containing no bijection: %d" % ((pi_cnt < 24).sum(), (C == 0).sum()))
print("tight classes containing no bijection: %d" % ((pi_cnt < 24) & (C == 0)).sum())
S = set(int(x) for x in gens); frontier = gens
gmid = np.concatenate([grow[:, np.argsort(IND[p])] for p in range(24)])
rnd = 0
while len(frontier):
    rnd += 1; new = set()
    for lo in range(0, len(frontier), 64):
        prod = compose(unpack(frontier[lo:lo + 64]), gmid).reshape(-1, 6)
        keys = np.unique(pack(prod))
        for c in np.unique(canon(keys)):
            if int(c) not in S: new.add(int(c))
    S |= new; frontier = np.array(sorted(new), dtype=np.uint64)
    print("round %d: %d classes (+%d) [%.0fs]" % (rnd, len(S), len(new), time.time() - t0), flush=True)
Sarr = np.array(sorted(S), dtype=np.uint64); Srow = unpack(Sarr)
bad = ~meets(Srow, IND).all(axis=1)
print("bad product classes: %d of %d" % (bad.sum(), len(Sarr)))
nonabs = (pi_cnt < 24).copy()
Smid = np.concatenate([Srow[:, np.argsort(IND[p])] for p in range(24)])
extra = 0
for gi in range(len(gens)):
    if nonabs[gi]: continue
    for lo in range(0, len(Smid), 8192):
        prod = compose(grow[gi:gi + 1], Smid[lo:lo + 8192]).reshape(-1, 6)
        if not meets(prod, IND).all():
            extra += 1; break
print("slack generators (Pi = 24) occurring in a bad cycle: %d  [%.0fs]" % (extra, time.time() - t0))
CS = contains(Srow, IND).sum(axis=1)
print("product classes containing no bijection: %d of %d" % ((CS == 0).sum(), len(Sarr)))
np.save(os.path.join(SP, "S_union.npy"), Sarr); np.save(os.path.join(SP, "gens_union.npy"), gens)
