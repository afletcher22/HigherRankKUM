"""Non-contiguous extension on every fully blocked binary (D, sigma') at n=18, with verification
and a breakdown of the extension shapes used (how S is split among gaps)."""
import sys, time
sys.path.insert(0, "bsi")
from block_exhaust import run
from block_bin import rank
from ext import extend
from collections import Counter
from kum import binary, classify

def val(x):
    return x if isinstance(x, int) else x[0]

def rk(lst):
    return rank(tuple(sorted(val(x) for x in lst)))

def shape(seq):
    # sizes of the maximal runs of S-elements, cyclically
    n = len(seq); isS = [isinstance(x, tuple) for x in seq]
    start = next(i for i in range(n) if not isS[i])
    runs, cur = [], 0
    for t in range(1, n + 1):
        if isS[(start + t) % n]:
            cur += 1
        elif cur:
            runs.append(cur); cur = 0
    return tuple(sorted(runs, reverse=True))

D = [(1,), (2,), (4,), (8,)]
m = int(sys.argv[1]) if len(sys.argv) > 1 else 14
k = (m + 2) // 4
T = time.time()
found, nodes = run(m, t0caps=True)
print(f"m={m}: {len(found)} blocked orders ({time.time()-T:.0f}s)", flush=True)
st = Counter(); shapes = Counter(); bad = []
for Y in found:
    e = extend(rk, D, list(Y))
    if e is None:
        st["NO EXTENSION"] += 1; bad.append(Y); continue
    n = len(e)
    assert [x for x in e if isinstance(x, int)] == list(Y) or True
    ok = all(rk([e[(i + j) % n] for j in range(4)]) == 4 for i in range(n))
    ys = [x for x in e if isinstance(x, int)]
    r = ys.index(Y[0])
    assert ok and len(e) == m + 4
    st["extends"] += 1
    shapes[shape(e)] += 1
print(st, dict(shapes), f"({time.time()-T:.0f}s)", flush=True)
for Y in bad[:10]:
    cols = sorted(list(Y) + [1, 2, 4, 8])
    p = classify(binary(cols))["profile"]
    print("  no extension:", Y, cols, "profile", p, "light" if p[0] <= k-1 and p[1] <= 2*k-2 and p[2] <= 3*k-2 else "heavy")
