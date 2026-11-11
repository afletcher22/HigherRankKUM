"""Do the cyclic-window invariants span all SL_r-invariants of multidegree (r,...,r)?

For n vectors v_1..v_n in F^r and a cyclic order s, P_s(v) = product over i of
det(v_{s(i)}, ..., v_{s(i+r-1)}).  P_s(v) != 0 exactly when s is a cyclic basis ordering of the
matroid of v.  Every P_s is an SL_r-invariant of multidegree (r, ..., r).  The space of all such
invariants has dimension the Kostka number K = #SSYT of shape (n^r) and content (r^n).

If the P_s span that space, then (char 0, representable matroids) uniform density implies a
cyclic basis ordering: a semistable configuration has a nonvanishing invariant of that
multidegree, so some P_s is nonzero.

This computes K exactly and the rank of {P_s} modulo a large prime at random points.
"""
import itertools, random, sys, time
import numpy as np

P = 2_147_483_629  # prime < 2^31

def kostka(r, n):
    """# SSYT with r rows, n columns, each of 1..n used exactly r times."""
    subs = list(itertools.combinations(range(n), r))
    from functools import lru_cache
    @lru_cache(maxsize=None)
    def go(col, prev, used):
        if col == n:
            return 1
        tot = 0
        for c in subs:
            if prev is not None and any(c[i] < prev[i] for i in range(r)):
                continue
            u = list(used); ok = True
            for x in c:
                u[x] += 1
                if u[x] > r: ok = False; break
            if not ok: continue
            # each value still needs r - u[x] more copies; remaining columns = n - col - 1
            rem = n - col - 1
            if any(r - u[x] > rem for x in range(n)): continue
            tot += go(col + 1, c, tuple(u))
        return tot
    return go(0, None, tuple([0] * n))

def det_mod(M):
    M = [row[:] for row in M]; r = len(M); d = 1
    for c in range(r):
        piv = next((i for i in range(c, r) if M[i][c] % P), None)
        if piv is None: return 0
        if piv != c: M[c], M[piv] = M[piv], M[c]; d = -d
        d = d * M[c][c] % P
        inv = pow(M[c][c], P - 2, P)
        for i in range(c + 1, r):
            f = M[i][c] * inv % P
            if f:
                M[i] = [(a - f * b) % P for a, b in zip(M[i], M[c])]
    return d % P

def rank_mod(A):
    A = A.copy() % P; rk = 0; rows, cols = A.shape
    for c in range(cols):
        piv = None
        nz = np.nonzero(A[rk:, c])[0]
        if len(nz) == 0: continue
        piv = rk + nz[0]
        if piv != rk: A[[rk, piv]] = A[[piv, rk]]
        inv = pow(int(A[rk, c]), P - 2, P)
        A[rk] = (A[rk] * inv) % P
        f = A[:, c].copy(); f[rk] = 0
        nzr = np.nonzero(f)[0]
        if len(nzr):
            A[nzr] = (A[nzr] - (f[nzr, None] * A[rk][None, :]) % P) % P
        rk += 1
        if rk == rows: break
    return rk

def cyclic_orders(n):
    """cyclic orders of 0..n-1 up to rotation and reflection"""
    for p in itertools.permutations(range(1, n)):
        if p[0] < p[-1]:
            yield (0,) + p

def main(r, n, maxcols=None, seed=1):
    t0 = time.time()
    K = kostka(r, n)
    orders = list(cyclic_orders(n))
    rng = random.Random(seed)
    if maxcols and len(orders) > maxcols:
        orders = rng.sample(orders, maxcols)
    npts = min(K + 10, len(orders) + 10)
    subs = list(itertools.combinations(range(n), r))
    A = np.zeros((npts, len(orders)), dtype=np.int64)
    for t in range(npts):
        V = [[rng.randrange(P) for _ in range(r)] for _ in range(n)]
        dets = {}
        for s in subs:
            dets[s] = det_mod([V[i] for i in s])
        for j, o in enumerate(orders):
            val = 1
            for i in range(n):
                w = tuple(sorted(o[(i + a) % n] for a in range(r)))
                val = val * dets[w] % P     # sign is irrelevant for the span
                if val == 0: break
            A[t, j] = val
    rk = rank_mod(A)
    print("r=%d n=%d gcd=%d: dim of all invariants K=%d; cyclic orders used %d; rank of window invariants %d  -> %s  (%.0fs)" % (
        r, n, __import__('math').gcd(r, n), K, len(orders), rk,
        "SPAN" if rk == K else ("at least %d of %d" % (rk, K)), time.time() - t0), flush=True)

if __name__ == "__main__":
    for a in sys.argv[1:]:
        parts = list(map(int, a.split(",")))
        main(*parts)
