"""Rank induction test on strict binary matroids: rank r on n = r k elements.

For a sampled choice of removed elements (x0 and k-1 others), sample cyclic basis orderings sigma
of Q = (M / x0) | Y (rank r-1), and test whether the removed elements can be matched to the k
equally spaced slots of sigma (x0 is good at every slot).
Usage: python schemeR5.py r k n_matroids n_pairs n_sigma seed
"""
import itertools, random, sys, time

def rank2(vs):
    basis = []
    for v in vs:
        for b in basis:
            v = min(v, v ^ b)
        if v: basis.append(v)
    return len(basis)

def par(x): return bin(x).count("1") & 1

def flat_counts_ok(vecs, r, bound, must_vanish=None):
    """bound(d) = max number of listed vectors allowed in a subspace of dimension d < r.
    If must_vanish is given, only subspaces containing that vector are tested."""
    fs = [f for f in range(1, 1 << r) if must_vanish is None or par(f & must_vanish) == 0]
    masks = {f: sum(1 << i for i, v in enumerate(vecs) if par(f & v) == 0) for f in fs}
    for t in range(1, r):
        for S in itertools.combinations(fs, t):
            if rank2(S) != t: continue
            m = -1
            for f in S: m &= masks[f]
            cnt = bin(m & ((1 << len(vecs)) - 1)).count("1")
            if cnt > bound(r - t): return False
    return True

def strict_matroid(r, k, rng):
    n = r * k
    while True:
        vecs = [rng.randrange(1, 1 << r) for _ in range(n)]
        if rank2(vecs) != r: continue
        if flat_counts_ok(vecs, r, lambda d: k * d - 1):   # strictly dense: |F| < k r(F)
            return vecs

def sample_sigma(vecs, Y, x0, r, rng, node_limit=40000):
    """One cyclic order of Y with every (r-1)-window + x0 independent, by randomized DFS."""
    w = r - 1
    def ind(idx): return rank2([vecs[i] for i in idx] + [vecs[x0]]) == len(idx) + 1
    first = Y[0]; seq = [first]; used = {first}; nodes = [0]
    def rec():
        nodes[0] += 1
        if nodes[0] > node_limit: return None
        if len(seq) == len(Y):
            ext = seq + seq[: w - 1]
            for i in range(len(Y) - (w - 1), len(Y)):
                if not ind(ext[i:i + w]): return False
            return True
        cand = [y for y in Y if y not in used]; rng.shuffle(cand)
        for y in cand:
            seq.append(y)
            if len(seq) < w or ind(seq[-w:]):
                used.add(y); res = rec()
                if res: return True
                if res is None: return None
                used.discard(y)
            seq.pop()
        return False
    res = rec()
    return tuple(seq) if res else None

def extends(vecs, sigma, Xp, r, k):
    m = len(sigma); w = r - 1
    def ind(idx, x): return rank2([vecs[i] for i in idx] + [vecs[x]]) == len(idx) + 1
    best = 0
    for rot in range(w):
        slots = [rot + j * w for j in range(k)]
        good = {x: [q for q in slots if all(
            ind([sigma[(q - w + t + a) % m] for a in range(w)], x) for t in range(r))] for x in Xp}
        best = max(best, sum(1 for x in Xp if good[x]))
        for free in slots:
            rest = [q for q in slots if q != free]
            if any(all(q in good[x] for x, q in zip(Xp, perm)) for perm in itertools.permutations(rest)):
                return True, best
    return False, best

def main(r, k, n_mat, n_pairs, n_sigma, seed):
    rng = random.Random(seed); t0 = time.time(); n = r * k
    tot_sig = tot_ok = 0
    for mi in range(n_mat):
        vecs = strict_matroid(r, k, rng)
        pairs = dense = some = sig = ok = 0
        while pairs < n_pairs:
            x0 = rng.randrange(n)
            Xp = tuple(rng.sample([e for e in range(n) if e != x0], k - 1))
            Y = [e for e in range(n) if e != x0 and e not in Xp]
            pairs += 1
            # Q = (M/x0)|Y uniformly dense: every subspace W containing x0 has |W cap Y| <= k (dim W - 1)
            if not flat_counts_ok([vecs[y] for y in Y], r, lambda d: k * (d - 1), must_vanish=vecs[x0]):
                continue
            dense += 1
            seen = set(); got = False
            for _ in range(n_sigma):
                s = sample_sigma(vecs, Y, x0, r, rng)
                if s is None or s in seen: continue
                seen.add(s); sig += 1
                e, _b = extends(vecs, s, Xp, r, k)
                if e: ok += 1; got = True
            if got: some += 1
        tot_sig += sig; tot_ok += ok
        print("matroid %d: choices tried %d, with dense contraction %d, with some extending ordering %d; "
              "orderings sampled %d, extending %d (%.1f%%)  [%.0fs]" % (
                  mi, pairs, dense, some, sig, ok, 100.0 * ok / max(sig, 1), time.time() - t0), flush=True)
    print("TOTAL r=%d k=%d: orderings sampled %d, extending %d (%.1f%%)" % (
        r, k, tot_sig, tot_ok, 100.0 * tot_ok / max(tot_sig, 1)), flush=True)

if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
