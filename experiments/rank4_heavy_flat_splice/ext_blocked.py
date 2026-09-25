"""Test non-contiguous extension on the exhaustive binary fully-blocked (D, sigma') lists."""
import sys, time
sys.path.insert(0, "bsi")
from block_exhaust import run
from block_bin import rank
from ext import extend
from collections import Counter

def rk(lst):
    return rank(tuple(sorted(x if isinstance(x, int) else x[0] for x in lst)))

D = [(1,), (2,), (4,), (8,)]   # tagged so they are distinguishable from Y copies
for m in [int(a) for a in sys.argv[1:]] or [10]:
    T = time.time()
    found, nodes = run(m, t0caps=True)
    print(f"m={m}: {len(found)} blocked orders ({time.time()-T:.0f}s)", flush=True)
    st = Counter()
    bad = []
    for Y in found:
        e = extend(rk, D, list(Y))
        st["extends" if e else "NO EXTENSION"] += 1
        if not e:
            bad.append(Y)
    print(st, f"({time.time()-T:.0f}s)", flush=True)
    for Y in bad[:5]:
        print("  no extension:", Y, sorted(Y + [1, 2, 4, 8]))
