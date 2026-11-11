"""The slack criterion at the level of full orderings, for twisted chains of rank g = 3 or 4.

W, W' are bases of a rank-g matroid given by an invertible matrix A over F_q (columns of W' in
the basis W).  States are the g! orders of a block.  (sigma, tau) is a serial exchange iff
    det A[{sigma_1..sigma_t}, {tau_1..tau_t}] != 0   for t = 1, ..., g - 1.
A bijection pi : W -> W' acts on orders; the relation *meets* pi if (sigma, pi sigma) is serial
for some sigma, and it is *slack* if it meets all g! bijections.

The script collects the relations of GL_g(F_q), reduces them up to relabelling (S_g x S_g),
generates the semigroup of products and reports whether a slack relation ever occurs in a cycle
that does not close.

Usage: python slack_orders.py g q [max_classes]
"""
import itertools, sys, time
import numpy as np


def setup(g):
    global G, ORD, NS, IND, WORDS
    G = g
    ORD = list(itertools.permutations(range(g))); NS = len(ORD)
    oi = {o: i for i, o in enumerate(ORD)}
    # IND[p][s] = index of the order p o sigma_s
    IND = np.array([[oi[tuple(p[x] for x in o)] for o in ORD] for p in ORD])


def minors(q):
    """All relations of GL_g(F_q), as boolean arrays (n, NS, NS), deduplicated."""
    n = q ** (G * G)
    seen = {}
    chunk = 1 << 18
    subsets = {t: list(itertools.combinations(range(G), t)) for t in range(1, G)}
    for lo in range(0, n, chunk):
        idx = np.arange(lo, min(lo + chunk, n), dtype=np.int64)
        A = np.stack([(idx // q ** e % q) for e in range(G * G)], axis=1).reshape(-1, G, G)
        nz = {}
        for t in range(1, G):
            for Rw in subsets[t]:
                for C in subsets[t]:
                    nz[(Rw, C)] = det_mod(A[:, Rw][:, :, C], q) != 0
        inv = det_mod(A, q) != 0
        rel = np.ones((len(idx), NS, NS), dtype=bool)
        for i, s in enumerate(ORD):
            for j, u in enumerate(ORD):
                for t in range(1, G):
                    rel[:, i, j] &= nz[(tuple(sorted(s[:t])), tuple(sorted(u[:t])))]
        rel = rel[inv]
        packed = np.packbits(rel.reshape(len(rel), -1), axis=1)
        _, first = np.unique(packed, axis=0, return_index=True)
        for f in first: seen[packed[f].tobytes()] = rel[f]
    return np.array(list(seen.values()))


def det_mod(M, q):
    M = M.copy() % q; n, m, _ = M.shape
    if m == 1: return M[:, 0, 0]
    if m == 2: return (M[:, 0, 0] * M[:, 1, 1] - M[:, 0, 1] * M[:, 1, 0]) % q
    return sum((-1) ** c * M[:, 0, c] * det_mod(np.delete(M[:, 1:], c, axis=2), q) for c in range(m)) % q


def canon(rels):
    """Canonical packed form under relabelling rows and columns."""
    best = None
    for p1 in range(NS):
        r1 = rels[:, np.argsort(IND[p1])]
        for p2 in range(NS):
            pk = np.packbits(r1[:, :, np.argsort(IND[p2])].reshape(len(rels), -1), axis=1)
            if best is None: best = pk
            else:
                # lexicographic minimum row-wise
                diff = pk != best
                firstdiff = diff.argmax(axis=1)
                rows = np.arange(len(pk))
                less = diff.any(axis=1) & (pk[rows, firstdiff] < best[rows, firstdiff])
                best = np.where(less[:, None], pk, best)
    return best


def unpack(pk):
    return np.unpackbits(pk, axis=1)[:, :NS * NS].reshape(len(pk), NS, NS).astype(bool)


def uniq(pk):
    return np.unique(pk, axis=0)


def meets(rels):
    """(n, NS) : relation n meets bijection p."""
    return np.stack([rels[:, np.arange(NS), IND[p]].any(axis=1) for p in range(NS)], axis=1)


def main():
    g, q = int(sys.argv[1]), int(sys.argv[2])
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 200000
    setup(g); t0 = time.time()
    raw = minors(q)
    gens = unpack(uniq(canon(raw)))
    slack = meets(gens).all(axis=1)
    print("g=%d, F_%d: %d relations, %d classes, %d slack, %d tight  [%.0fs]" % (
        g, q, len(raw), len(gens), slack.sum(), (~slack).sum(), time.time() - t0), flush=True)
    # middle relabellings of the generators
    gmid = np.concatenate([gens[:, np.argsort(IND[p])] for p in range(NS)]).astype(np.uint8)
    S = {r.tobytes() for r in uniq(canon(gens))}
    frontier = gens; rnd = 0
    while len(frontier) and len(S) < cap:
        rnd += 1; new = {}
        for lo in range(0, len(frontier), 8):
            P = frontier[lo:lo + 8].astype(np.uint8)
            prod = (np.einsum("aij,bjk->abik", P, gmid) > 0).reshape(-1, NS, NS)
            pk = uniq(np.packbits(prod.reshape(len(prod), -1), axis=1))
            for c in uniq(canon(unpack(pk))):
                b = c.tobytes()
                if b not in S: new[b] = c
        S |= set(new)
        frontier = unpack(np.array(list(new.values()))) if new else np.zeros((0, NS, NS), dtype=bool)
        print("round %d: %d classes (+%d)  [%.0fs]" % (rnd, len(S), len(new), time.time() - t0), flush=True)
    complete = len(frontier) == 0
    Sarr = unpack(np.array([np.frombuffer(b, dtype=np.uint8) for b in S]))
    bad = ~meets(Sarr).all(axis=1)
    print("semigroup %s: %d classes, %d with a labelling that does not close" % (
        "complete" if complete else "TRUNCATED", len(Sarr), bad.sum()))
    # slack generator g, any product P (with a relabelling in the middle): does g.P always close?
    Smid = np.concatenate([Sarr[:, np.argsort(IND[p])] for p in range(NS)]).astype(np.uint8)
    viol = 0
    for gi in np.nonzero(slack)[0]:
        for lo in range(0, len(Smid), 2048):
            prod = np.einsum("ij,bjk->bik", gens[gi].astype(np.uint8), Smid[lo:lo + 2048]) > 0
            if not meets(prod).all():
                viol += 1; break
    print("slack classes occurring in a cycle that does not close: %d of %d  [%.0fs]" % (
        viol, slack.sum(), time.time() - t0))
    contains = np.stack([gens[:, np.arange(NS), IND[p]].all(axis=1) for p in range(NS)], axis=1).any(axis=1)
    print("classes containing a bijection: %d; tight classes containing none: %d" % (
        contains.sum(), (~slack & ~contains).sum()))


if __name__ == "__main__":
    main()
