"""All matroids of rank 4 on W + W' (|W| = |W'| = 4) in which W and W' are bases.

A matroid is a set of 4-subsets containing W and W'.  The search fixes the level-1 exchange graph
(W - a + b a basis) up to S_4 x S_4, then assigns the 36 sets meeting W in two elements and the 16
meeting it in one, pruning with the octahedron (3-term) condition; every leaf is then checked
against the basis exchange axiom for pairs of bases at distance 3 and 4.  No SAT solver.

Output: the distinct level-2 relations  T(P, P') = [(W - P) + P' is a basis]  as 36-bit integers
(bit 6 i + j for the i-th pair P of W and the j-th pair P' of W').

Usage: python slack_allmatroids.py out.npy
"""
import itertools, sys, time
import numpy as np

PAIRS = list(itertools.combinations(range(4), 2)); PI = {p: i for i, p in enumerate(PAIRS)}
S4 = list(itertools.permutations(range(4)))
WM, WP = 0x0F, 0xF0
SETS = [sum(1 << e for e in c) for c in itertools.combinations(range(8), 4)]
pc = lambda x: bin(x).count("1")
def els(x): return [e for e in range(8) if x >> e & 1]

def var(X):
    """(kind, bit): kind 0 const true, 1 bit of lo, 2 bit of hi; order index for completion."""
    l = pc(X & WP)
    if l in (0, 4): return (0, 0, -2)
    if l == 1:
        a = els(WM & ~X)[0]; b = els(X & WP)[0] - 4
        return (1, 4 * a + b, -1)
    if l == 2:
        P = tuple(els(WM & ~X)); Pp = tuple(e - 4 for e in els(X & WP))
        j = 6 * PI[P] + PI[Pp]
        return (1, 16 + j, j)
    a = els(X & WM)[0]; b = els(WP & ~X)[0] - 4
    return (2, 4 * a + b, 36 + 4 * a + b)

CONS = {}
for I in itertools.combinations(range(8), 2):
    rest = [e for e in range(8) if e not in I]; Im = (1 << I[0]) | (1 << I[1])
    for Q in itertools.combinations(rest, 4):
        a, b, c, d = Q
        trip = []
        for (x, y), (z, t) in (((a, b), (c, d)), ((a, c), (b, d)), ((a, d), (b, c))):
            trip.append((var(Im | 1 << x | 1 << y), var(Im | 1 << z | 1 << t)))
        step = max(v[2] for pr in trip for v in pr)
        if step == -2: continue
        CONS.setdefault(step, []).append(trip)

def val(v, lo, hi):
    if v[0] == 0: return np.ones(len(lo), dtype=bool)
    src = lo if v[0] == 1 else hi
    return ((src >> np.uint64(v[1])) & np.uint64(1)).astype(bool)

def check(step, lo, hi):
    keep = np.ones(len(lo), dtype=bool)
    for trip in CONS.get(step, []):
        cnt = np.zeros(len(lo), dtype=np.int8)
        for u, v in trip: cnt += (val(u, lo, hi) & val(v, lo, hi))
        keep &= cnt != 1
    return keep

# exact basis exchange for pairs at distance >= 3 (distance 2 is the octahedron condition)
IDX = {X: i for i, X in enumerate(SETS)}
EXCH = []
for X in SETS:
    for Y in SETS:
        if pc(X & ~Y) < 3: continue
        for x in els(X & ~Y):
            EXCH.append((X, Y, [(X & ~(1 << x)) | (1 << y) for y in els(Y & ~X)]))

def exact(lo, hi):
    cols = {X: val(var(X), lo, hi) for X in SETS}
    ok = np.ones(len(lo), dtype=bool)
    for X, Y, cand in EXCH:
        both = cols[X] & cols[Y]
        if not both.any(): continue
        any_ = cols[cand[0]].copy()
        for Z in cand[1:]: any_ |= cols[Z]
        ok &= ~both | any_
    return ok

CAP = 400000
LEAF = None
stats = {"leaves": 0, "octa_only": 0}
found = set()

def run(lo, hi, step):
    while step < 52:
        if step < 36:
            lo = np.concatenate([lo, lo | np.uint64(1 << (16 + step))]); hi = np.concatenate([hi, hi])
        else:
            hi = np.concatenate([hi, hi | np.uint64(1 << (step - 36))]); lo = np.concatenate([lo, lo])
        k = check(step, lo, hi); lo, hi = lo[k], hi[k]
        step += 1
        if not len(lo): return
        if len(lo) > CAP and step < 52:
            for s in range(0, len(lo), CAP // 2): run(lo[s:s + CAP // 2], hi[s:s + CAP // 2], step)
            return
    stats["octa_only"] += len(lo)
    k = exact(lo, hi); lo, hi = lo[k], hi[k]
    stats["leaves"] += len(lo)
    if LEAF: LEAF(lo, hi)
    found.update(np.unique(lo >> np.uint64(16)).tolist())

def g1_reps():
    pat = np.arange(1 << 16)
    M = ((pat[:, None] >> np.arange(16)) & 1).reshape(-1, 4, 4)
    pm = np.zeros(len(pat), dtype=bool)
    for p in S4:
        t = np.ones(len(pat), dtype=bool)
        for i in range(4): t &= M[:, i, p[i]] == 1
        pm |= t
    best = np.full(len(pat), 1 << 16)
    wts = (1 << np.arange(16)).reshape(4, 4)
    for p in S4:
        for q in S4:
            best = np.minimum(best, (M[:, list(p)][:, :, list(q)] * wts).sum(axis=(1, 2)))
    return sorted(set(best[pm].tolist()))

if __name__ == "__main__":
    t0 = time.time(); reps = g1_reps()
    print("level-1 graphs with a perfect matching, up to S4 x S4: %d" % len(reps), flush=True)
    for n, g in enumerate(reps):
        lo = np.array([g], dtype=np.uint64); hi = np.zeros(1, dtype=np.uint64)
        if not check(-1, lo, hi).all(): continue
        before = stats["leaves"]
        run(lo, hi, 0)
        if n % 20 == 0 or stats["leaves"] - before > 100000:
            print("graph %d/%d (%04x): %d matroids, total %d, relations %d  [%.0fs]" % (
                n, len(reps), g, stats["leaves"] - before, stats["leaves"], len(found), time.time() - t0), flush=True)
    print("TOTAL matroids (level-1 graph up to symmetry): %d; passing octahedra only: %d; distinct relations: %d  [%.0fs]" % (
        stats["leaves"], stats["octa_only"], len(found), time.time() - t0))
    np.save(sys.argv[1], np.array(sorted(found), dtype=np.uint64))
