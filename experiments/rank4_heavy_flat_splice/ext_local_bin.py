"""Local extension in binary rank 4: count linear sequences Y (4-windows bases, values in
GF(2)^4-0, Y[0] an S4-orbit representative) into whose interior S={1,2,4,8} cannot be
interleaved, by length.  If the count reaches 0 at length L*, Conjecture E holds for every binary
rank-4 matroid with |E-S| >= L* (no density hypothesis)."""
import sys, time
from collections import Counter
from ext_bin_exhaust import advance, rank
from block_bin import PTS

def survivors(Lmax, caps=None):
    cnt = Counter()
    level = []
    for y0 in (1, 3, 7, 15):
        level.append(((y0,), frozenset({(0, (y0,), 1)})))
    cnt[1] = len(level)
    for L in range(2, Lmax + 1):
        nxt = []
        for Y, st in level:
            for v in PTS:
                w = list(Y[-3:]) + [v]
                if rank(tuple(sorted(w))) != len(w):
                    continue
                nst = advance(set(st), v)
                if any(u == 15 and t >= 3 for u, _, t in nst):
                    continue
                nxt.append((Y + (v,), frozenset(nst)))
        # merge identical (last3, state) to keep it small: survival only depends on them
        merged = {}
        for Y, st in nxt:
            key = (Y[-3:], st)
            if key not in merged:
                merged[key] = Y
        level = [(Y, st) for (l3, st), Y in merged.items()]
        cnt[L] = len(level)
        print(f"L={L}: surviving classes={len(level)}", flush=True)
        if not level:
            break
    return cnt, level

if __name__ == "__main__":
    T = time.time()
    cnt, level = survivors(int(sys.argv[1]) if len(sys.argv) > 1 else 20)
    print(f"({time.time()-T:.0f}s)")
    for Y, st in level[:5]:
        print("example survivor:", Y)
