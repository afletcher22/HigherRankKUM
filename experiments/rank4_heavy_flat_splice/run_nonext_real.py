"""Adversarial real-matroid check of the extension theorem: for random GF(3)/GF(5)/GF(7) and
sparse paving rank-4 matroids with |E-S| = 8..10, search (limited DFS) for a CBO of M-S with no
extension.  Theorem X' predicts none."""
import sys, random, itertools, time
from collections import Counter
from kum import *
from gen import proj_points, mk
from nonext import nonext_orders

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
NI = int(sys.argv[2]) if len(sys.argv) > 2 else 30
T = time.time()
stats = Counter()
def sp(n):
    fam = []
    for _ in range(rng.randint(n, 4 * n)):
        c = tuple(sorted(rng.sample(range(n), 4)))
        if all(len(set(c) & set(d)) <= 2 for d in fam):
            fam.append(c)
    return sparse_paving(n, fam)
for n in (12, 13, 14):
    for kind in ("gf3", "gf5", "gf7", "sp"):
        for it in range(NI):
            if kind == "sp":
                M = sp(n)
            else:
                p = int(kind[2:])
                pts = proj_points(p, 4)
                base = rng.sample(pts, rng.randint(5, min(len(pts), n)))
                vecs = []
                while len(vecs) < n:
                    vecs.append(rng.choice(vecs) if vecs and rng.random() < 0.35 else rng.choice(base))
                M = mk(p, vecs)
            if M.rank() != 4:
                continue
            bases = [B for B in itertools.combinations(range(n), 4) if M.rk(B) == 4]
            S = list(rng.choice(bases))
            f, st, nodes = nonext_orders(M, S, limit=2 * 10 ** 5, rng=rng)
            stats[(n, kind, "NONEXT" if f else st)] += 1
            if f:
                print("NONEXT!", n, kind, S, f[0], flush=True)
        print(n, kind, {k[2]: v for k, v in stats.items() if k[:2] == (n, kind)}, f"{time.time()-T:.0f}s", flush=True)
