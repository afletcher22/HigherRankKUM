"""Cyclic chains of k disjoint bases (divisible case, q = 1).

For bases B_1..B_k of a rank-r matroid, in a fixed cyclic order:
  subset(c):  T_i in B_i, |T_i| = c, with (B_i - T_i) + T_{i+1} a basis for all i (cyclically)
  interval:   linear orders of each B_i such that B_1 B_2 ... B_k is a cyclic basis ordering
Both are closed walks through relations between consecutive bases, decided by boolean
matrix products.  Falsification tests only.
"""
import itertools, random, sys
import numpy as np


def rank_gfp(vecs, p):
    rows = [list(v) for v in vecs]
    rk = 0
    for c in range(len(rows[0])):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c] % p), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][c], p - 2, p)
        rows[rk] = [(x * inv) % p for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c] % p:
                f = rows[i][c]
                rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[rk])]
        rk += 1
    return rk


def base_table(vecs, p, r):
    tab = set()
    for c in itertools.combinations(range(len(vecs)), r):
        if rank_gfp([vecs[i] for i in c], p) == r:
            tab.add(sum(1 << i for i in c))
    return tab


def subset_rel(B, Bn, c, tab):
    r = len(B)
    subs = list(itertools.combinations(range(r), c))
    R = np.zeros((len(subs), len(subs)), dtype=bool)
    for i, T in enumerate(subs):
        rest = sum(1 << B[x] for x in range(r) if x not in T)
        for j, Tn in enumerate(subs):
            R[i, j] = (rest | sum(1 << Bn[x] for x in Tn)) in tab
    return R


def serial_rel(B, Bn, tab, perms):
    r = len(B)
    R = np.zeros((len(perms), len(perms)), dtype=bool)
    suf = [[sum(1 << B[x] for x in p[t:]) for t in range(1, r)] for p in perms]
    pre = [[sum(1 << Bn[x] for x in p[:t]) for t in range(1, r)] for p in perms]
    for i, s in enumerate(suf):
        for j, q in enumerate(pre):
            R[i, j] = all((s[t] | q[t]) in tab for t in range(r - 1))
    return R


def closed(rels):
    P = rels[0]
    for R in rels[1:]:
        P = (P.astype(np.uint8) @ R.astype(np.uint8)) > 0
    return bool(P.diagonal().any())


def analyse(bases, tab, perms):
    """bases: list of k tuples of element indices.  Returns dict of results per cyclic order."""
    k = len(bases)
    r = len(bases[0])
    out = {}
    orders = [tuple(range(k))] if k == 2 else [tuple(range(k)), (0,) + tuple(range(k - 1, 0, -1))]
    for o in orders:
        seq = [bases[i] for i in o]
        res = {}
        for c in range(1, r):
            res[c] = closed([subset_rel(seq[i], seq[(i + 1) % k], c, tab) for i in range(k)])
        res["interval"] = closed([serial_rel(seq[i], seq[(i + 1) % k], tab, perms) for i in range(k)])
        out[o] = res
    return out


def random_bases(r, k, p, rng):
    out = []
    for _ in range(k):
        while True:
            B = [tuple(rng.randrange(p) for _ in range(r)) for _ in range(r)]
            if rank_gfp(B, p) == r:
                out.append(B)
                break
    return out


def run(r, k, p, trials, seed):
    rng = random.Random(seed)
    perms = list(itertools.permutations(range(r)))
    stats = {}
    bad = []
    for _ in range(trials):
        Bs = random_bases(r, k, p, rng)
        vecs = [v for B in Bs for v in B]
        tab = base_table(vecs, p, r)
        bases = [tuple(range(i * r, (i + 1) * r)) for i in range(k)]
        res = analyse(bases, tab, perms)
        for o, d in res.items():
            for key, val in d.items():
                s = stats.setdefault(key, [0, 0])
                s[0] += 1
                s[1] += val
        any_interval = any(d["interval"] for d in res.values())
        all_interval = all(d["interval"] for d in res.values())
        s = stats.setdefault("interval_some_order", [0, 0]); s[0] += 1; s[1] += any_interval
        s = stats.setdefault("interval_every_order", [0, 0]); s[0] += 1; s[1] += all_interval
        if not all(all(d.values()) for d in res.values()) and len(bad) < 3:
            bad.append((Bs, res))
    print("r=%d k=%d GF(%d) trials=%d" % (r, k, p, trials))
    for key, (tot, ok) in stats.items():
        print("   %-22s holds %d / %d" % (key, ok, tot))
    for Bs, res in bad:
        print("   failure example:", Bs, res)
    sys.stdout.flush()


if __name__ == "__main__":
    spec = sys.argv[1:]
    for s in spec:
        r, k, p, trials = map(int, s.split(","))
        run(r, k, p, trials, 7)
