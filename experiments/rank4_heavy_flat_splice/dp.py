"""Decomposition principle (DP) for a plane K of a rank-4 matroid M.

K = K0 + T1 + ... + Tm  (Ti bases of M|K),  C = C0 + {c1..cm}  (C = E - K).
If M0 = M|(K0 + C0) has a CBO containing a K-site (pattern 1011101), then repeated
heavy-flat splices (Theorem 4, rho=3) with Bi = Ti + {ci} give a CBO of M.
No density hypothesis on intermediate matroids is needed.
"""
import itertools, random
from kum import *
from bsl import two_gap


def has_site(order, K):
    n = len(order)
    f = [(K >> x) & 1 for x in order]
    for i in range(n):
        if [f[(i + j) % n] for j in range(7)] == [1, 0, 1, 1, 1, 0, 1]:
            return i
    return None


def site_cbo(M, elems, K, limit=10 ** 6):
    """DFS over CBOs of M|elems; return the first one with a K-site (or None)."""
    found = []
    elems = list(elems)
    try:
        for o in _cbo_iter(M, elems, limit):
            if has_site(o, K) is not None:
                return list(o)
    except Timeout:
        return "timeout"
    return None


def _cbo_iter(M, elems, limit):
    n = len(elems)
    first = elems[0]
    order = [first]
    used = {first}
    cnt = [0]

    def okw(w):
        return M.rk(w) == len(w) and len(set(w)) == len(w)

    def dfs():
        cnt[0] += 1
        if cnt[0] > limit:
            raise Timeout
        L = len(order)
        if L == n:
            if all(okw([order[(i + j) % n] for j in range(4)]) for i in range(n - 3, n)):
                yield tuple(order)
            return
        for e in elems:
            if e in used:
                continue
            order.append(e)
            if okw(order[-4:] if L + 1 >= 4 else order):
                used.add(e)
                yield from dfs()
                used.discard(e)
            order.pop()
    yield from dfs()


def splice_plane(M, K, T, c, sigma):
    """Theorem 4 (rho=3) at the first K-site of sigma."""
    n = len(sigma)
    i = has_site(sigma, K)
    if i is None:
        return None
    w, u, x1, x2, x3, v, y = (sigma[(i + j) % n] for j in range(7))
    g = two_gap(M, list(T), w, x1, x2, x3, y)
    assert g is not None, "two-gap failed"
    kind, d = g
    block = ([x1, d[0], d[1], c, d[2], x2, x3] if kind == "first"
             else [x1, x2, d[0], c, d[1], d[2], x3])
    rot = [sigma[(i + 2 + j) % n] for j in range(n)]
    return block + rot[3:]


def rank3_dense(M, S, m):
    """M|S (|S|=3m) partitions into m bases of the rank-3 flat  <=>  |X|<=m r(X)."""
    if M.r(S) != 3:
        return False
    fl = M.flats(S)
    return all(pc(F) <= m for F in fl[1]) and all(pc(F) <= 2 * m for F in fl[2])


def partition_into_bases(M, S):
    """greedy+backtrack partition of S (|S|=3m, rank-3 dense) into independent triples."""
    els = bits(S)
    m = len(els) // 3
    blocks = []

    def rec(rem):
        if not rem:
            return True
        a = rem[0]
        for b, c in itertools.combinations(rem[1:], 2):
            if M.rk([a, b, c]) == 3:
                rest = [x for x in rem if x not in (a, b, c)]
                sub = sum(1 << x for x in rest)
                if not rest or rank3_dense(M, sub, len(rest) // 3):
                    blocks.append((a, b, c))
                    if rec(rest):
                        return True
                    blocks.pop()
        return False
    return blocks if rec(els) else None


def dp_construct(M, K, K0, C0, sigma0):
    """build a CBO of M from a site-CBO sigma0 of M|(K0+C0)."""
    Kl = bits(K)
    C = [x for x in range(M.n) if not (K >> x) & 1]
    S = K & ~sum(1 << x for x in K0)
    blocks = partition_into_bases(M, S)
    assert blocks is not None
    rest = [c for c in C if c not in C0]
    assert len(rest) == len(blocks)
    sigma = list(sigma0)
    for T, c in zip(blocks, rest):
        sigma = splice_plane(M, K, T, c, sigma)
        assert sigma is not None
    return sigma
