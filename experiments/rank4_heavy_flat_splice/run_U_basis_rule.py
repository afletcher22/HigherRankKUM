"""For the light binary matroids with a blocked (D, sigma') at n=18, classify EVERY basis D' as
universal / non-universal (exact: map D' to the standard basis by GL(4,2) and test membership in
the exhaustive blocked set), and look for the feature separating them."""
import sys, json, os, itertools, time
from collections import Counter
sys.path.insert(0, "bsi")
from block_exhaust import run
from kum import binary, classify, gf2_rank
T = time.time()
cache = "blocked_n18.json"
if os.path.exists(cache):
    blocked = {tuple(x) for x in json.load(open(cache))}
else:
    found, _ = run(14, t0caps=True)
    blocked = {tuple(sorted(Y + [1, 2, 4, 8])) for Y in found}
    json.dump(sorted(blocked), open(cache, "w"))
print("blocked multisets:", len(blocked), f"{time.time()-T:.0f}s", flush=True)

def coords(v, Dp):
    for c in range(1, 16):
        s = 0
        for j in range(4):
            if (c >> j) & 1:
                s ^= Dp[j]
        if s == v:
            return c

def light(cols, k):
    p = classify(binary(cols))["profile"]
    return p[0] <= k - 1 and p[1] <= 2 * k - 2 and p[2] <= 3 * k - 2

k = 4
lights = [ms for ms in blocked if light(ms, k)]
print("light blocked matroids:", len(lights), flush=True)
feat = Counter()
for cols in lights:
    cols = list(cols); M = binary(cols); n = len(cols)
    mult = Counter(cols)
    types = {}
    for Dd in itertools.combinations(range(n), 4):
        key = tuple(sorted(cols[i] for i in Dd))
        if key in types or M.rk(Dd) != 4:
            continue
        Dp = [cols[i] for i in Dd]
        img = tuple(sorted(coords(v, Dp) for v in cols))
        types[key] = img in blocked
    bad = [key for key, v in types.items() if v]
    good = [key for key, v in types.items() if not v]
    # features: number of basis elements whose point has multiplicity >= 2 in M
    def mates(key):
        return sum(1 for v in set(key) if mult[v] >= 2) if len(set(key)) == 4 else -1
    for key in bad:
        feat[("BAD", "elements with parallel mate", mates(key))] += 1
    for key in good:
        feat[("good", "elements with parallel mate", mates(key))] += 1
    print(cols, "basis types:", len(types), "non-universal:", bad, flush=True)
for k_, v in sorted(feat.items()):
    print(k_, v)
print(f"{time.time()-T:.0f}s")
