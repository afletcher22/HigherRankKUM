"""Exact binary test of Conjecture U: among ALL fully blocked (M, D=standard basis, sigma') at
n=14 and n=18 (block_exhaust, strict t=0 caps, M-D uniformly dense), is any M light?
(GL(4,2) is transitive on ordered bases, so D = standard basis is WLOG for binary.)"""
import sys, time
sys.path.insert(0, ".")
sys.path.insert(0, "..")
from block_exhaust import run
from kum import binary, classify
from collections import Counter
for m in (10, 14):
    t = time.time()
    found, nodes = run(m, t0caps=True)
    n = m + 4; k = (n - 2) // 4
    ms = {tuple(sorted(Y + [1, 2, 4, 8])) for Y in found}
    c = Counter()
    for cols in ms:
        M = binary(cols); p = classify(M)["profile"]
        light = p[0] <= k - 1 and p[1] <= 2 * k - 2 and p[2] <= 3 * k - 2
        tags = [] if light else [s for s, cond in (("pt>=k", p[0] >= k), ("ln>=2k-1", p[1] >= 2 * k - 1), ("pl>=3k-1", p[2] >= 3 * k - 1)) if cond]
        c["LIGHT" if light else "heavy:" + "+".join(tags)] += 1
        if light: print("  LIGHT blocked M:", cols, p, flush=True)
    print(f"n={n}: blocked sequences={len(found)} blocked matroids={len(ms)} -> {dict(c)} ({time.time()-t:.0f}s)", flush=True)
