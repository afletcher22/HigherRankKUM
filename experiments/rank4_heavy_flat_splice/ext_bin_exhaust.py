"""EXHAUSTIVE binary test of Conjecture E: every cyclic sequence Y of GF(2)^4 values (length m)
whose 4-windows are bases, i.e. every CBO of every binary M-S, extends by S = {1,2,4,8}
(one copy each; WLOG by GL(4,2)).  DFS over Y with Y[0] in {1,3,7,15} (S4 orbit representatives),
pruned when S already interleaves into the interior of the prefix.  Optional caps on M
(strict t=0 caps k,2k,3k) to restrict to the strict class."""
import sys, time
sys.path.insert(0, "bsi")
from block_bin import rank, PTS, LINES_OF, PLANES_OF, LINES, PLANES
from ext import extend
sys.setrecursionlimit(100000)

S = [(1,), (2,), (4,), (8,)]
def val(x):
    return x if isinstance(x, int) else x[0]
def rk(lst):
    return rank(tuple(sorted(val(x) for x in lst)))

def close(states):
    out = set(states); st = list(states)
    while st:
        used, l3, tail = st.pop()
        if used == 15 or len(l3) < 3:
            continue
        for j in range(4):
            if used >> j & 1:
                continue
            w = list(l3) + [S[j]]
            if rk(w) == 4:
                s2 = (used | 1 << j, tuple(w[-3:]), 0)
                if s2 not in out:
                    out.add(s2); st.append(s2)
    return out

def advance(states, y):
    nxt = set()
    for used, l3, tail in states:
        w = list(l3) + [y]
        if rk(w) == len(w):
            nxt.add((used, tuple(w[-3:]), min(tail + 1, 3)))
    return close(nxt)

def run(m, strict=False):
    n = m + 4; k = (n - 2) // 4
    capY = (m / 4, m / 2, 3 * m / 4)
    capM = (k, 2 * k, 3 * k) if strict else (n / 4, n / 2, 3 * n / 4)
    cntY = {p: 0 for p in PTS}; lineY = [0] * len(LINES); planeY = [0] * len(PLANES)
    Dset = (1, 2, 4, 8)
    cntD = {p: (1 if p in Dset else 0) for p in PTS}
    lineD = [sum(1 for d in Dset if d in L) for L in LINES]
    planeD = [sum(1 for d in Dset if d in H) for H in PLANES]
    Y = []; stack = []; bad = []; nodes = [0]
    def add(v, s):
        cntY[v] += s
        for i in LINES_OF[v]: lineY[i] += s
        for i in PLANES_OF[v]: planeY[i] += s
    def caps_ok(v):
        if cntY[v] > capY[0] or cntY[v] + cntD[v] > capM[0]: return False
        for i in LINES_OF[v]:
            if lineY[i] > capY[1] or lineY[i] + lineD[i] > capM[1]: return False
        for i in PLANES_OF[v]:
            if planeY[i] > capY[2] or planeY[i] + planeD[i] > capM[2]: return False
        return True
    def dfs():
        nodes[0] += 1
        L = len(Y)
        if L == m:
            for i in range(m - 3, m):
                if rank(tuple(sorted(Y[(i + j) % m] for j in range(4)))) != 4:
                    return
            if extend(rk, S, list(Y)) is None:
                bad.append(list(Y))
            return
        for v in PTS:
            if L >= 3:
                if rank(tuple(sorted((Y[-3], Y[-2], Y[-1], v)))) != 4: continue
            elif rank(tuple(sorted(Y + [v]))) != L + 1: continue
            add(v, 1)
            if caps_ok(v):
                nst = advance(stack[-1], v)
                if not any(u == 15 and t >= 3 for u, _, t in nst):
                    Y.append(v); stack.append(nst)
                    dfs()
                    Y.pop(); stack.pop()
            add(v, -1)
    for y0 in (1, 3, 7, 15):
        add(y0, 1)
        if caps_ok(y0):
            Y.append(y0); stack.append({(0, (y0,), 1)})
            dfs()
            Y.pop(); stack.pop()
        add(y0, -1)
    return bad, nodes[0]

if __name__ == "__main__":
    strict = "strict" in sys.argv
    for m in [int(a) for a in sys.argv[1:] if a.isdigit()]:
        T = time.time()
        bad, nodes = run(m, strict)
        print(f"m={m} n={m+4} {'strict' if strict else 'all'}: non-extendable CBOs={len(bad)} nodes={nodes} ({time.time()-T:.0f}s)", flush=True)
        for Y in bad[:5]:
            print("   ", Y, sorted(Y + [1, 2, 4, 8]))
