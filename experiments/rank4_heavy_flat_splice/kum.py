"""Independent rank-4 KUM research toolkit (session 2026-09-24, scratchpad only).

Elements are 0..n-1; sets are int bitmasks.  Matroids are given by a rank oracle
with a bitmask cache.  GF(2) matroids use packed-int vectors, GF(p) use tuples.
"""
import itertools, random
from functools import lru_cache


def bits(x):
    out = []
    while x:
        b = x & -x
        out.append(b.bit_length() - 1)
        x ^= b
    return out


def pc(x):
    return bin(x).count("1")


# ---------------------------------------------------------------- rank oracles
def gf2_rank(vs):
    basis = []
    for v in vs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)


def gfp_rank(vecs, p):
    rows = [list(v) for v in vecs]
    if not rows:
        return 0
    r = 0
    nc = len(rows[0])
    for c in range(nc):
        piv = None
        for i in range(r, len(rows)):
            if rows[i][c] % p:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][c], p - 2, p)
        rows[r] = [(x * inv) % p for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % p:
                f = rows[i][c]
                rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[r])]
        r += 1
        if r == len(rows):
            break
    return r


class Mat:
    def __init__(self, n, rank_of_list, name="", data=None):
        self.n = n
        self._rl = rank_of_list
        self.name = name
        self.data = data
        self.cache = {0: 0}
        self.full = (1 << n) - 1

    def r(self, m):
        c = self.cache.get(m)
        if c is None:
            c = self._rl(bits(m))
            self.cache[m] = c
        return c

    def rk(self, elems):
        m = 0
        for e in elems:
            m |= 1 << e
        return self.r(m)

    def cl(self, m):
        rr = self.r(m)
        out = m
        for y in range(self.n):
            if not (m >> y) & 1 and self.r(m | (1 << y)) == rr:
                out |= 1 << y
        return out

    def rank(self):
        return self.r(self.full)

    def is_basis(self, elems):
        return len(set(elems)) == 4 and self.rk(elems) == 4

    # flats of rank 1..3 restricted to a ground mask
    def flats(self, ground=None):
        if ground is None:
            ground = self.full
        els = bits(ground)
        fl = {1: set(), 2: set(), 3: set()}
        def clg(m):
            return self.cl(m) & ground
        for a in els:
            if self.r(1 << a) == 1:
                fl[1].add(clg(1 << a))
        F1 = sorted(fl[1])
        for i in range(len(F1)):
            for j in range(i + 1, len(F1)):
                fl[2].add(clg(F1[i] | F1[j]))
        for L in sorted(fl[2]):
            for P in F1:
                if not (P & L):
                    m = clg(L | P)
                    if self.r(m) == 3:
                        fl[3].add(m)
        return fl

    def profile(self, ground=None):
        fl = self.flats(ground)
        return tuple(max((pc(F) for F in fl[j]), default=0) for j in (1, 2, 3))


def binary(cols, name="bin"):
    cols = tuple(cols)
    return Mat(len(cols), lambda L: gf2_rank([cols[i] for i in L]), name, cols)


def gfp(vecs, p, name=None):
    vecs = [tuple(v) for v in vecs]
    return Mat(len(vecs), lambda L: gfp_rank([vecs[i] for i in L], p), name or f"GF({p})", vecs)


def sparse_paving(n, chs, name="sp"):
    """rank-4 sparse paving: chs = list of 4-element circuit-hyperplanes."""
    chm = set(sum(1 << x for x in c) for c in chs)
    def rl(L):
        s = len(L)
        if s <= 3:
            return s
        if s == 4:
            m = sum(1 << x for x in L)
            return 3 if m in chm else 4
        return 4
    return Mat(n, rl, name, chs)


# ---------------------------------------------------------------- density
def classify(M):
    """Return dict with k, strict, t (number of dangerous planes), profile, planes3k."""
    n = M.n
    assert (n - 2) % 4 == 0
    k = (n - 2) // 4
    fl = M.flats()
    prof = tuple(max((pc(F) for F in fl[j]), default=0) for j in (1, 2, 3))
    strict = M.rank() == 4 and prof[0] <= k and prof[1] <= 2 * k and prof[2] <= 3 * k + 1
    t = sum(1 for F in fl[3] if pc(F) == 3 * k + 1)
    planes3k = [F for F in fl[3] if pc(F) == 3 * k]
    return dict(k=k, strict=strict, t=t, profile=prof, planes3k=planes3k, flats=fl)


# ---------------------------------------------------------------- CBO search
def is_cbo(M, order, r=4):
    n = len(order)
    return all(M.rk([order[(i + j) % n] for j in range(r)]) == r and
               len({order[(i + j) % n] for j in range(r)}) == r for i in range(n))


class Timeout(Exception):
    pass


def find_cbo(M, elems=None, r=4, first=None, limit=10 ** 7, rng=None, want_all=False):
    """DFS for cyclic order of elems with every r consecutive independent of size r
    and rank r.  Returns an order, None, or list (want_all)."""
    elems = list(range(M.n)) if elems is None else list(elems)
    n = len(elems)
    first = elems[0] if first is None else first
    order = [first]
    used = 1 << first
    out = []
    cnt = [0]

    def okw(w):
        m = 0
        for x in w:
            m |= 1 << x
        return M.r(m) == len(w)

    def dfs():
        nonlocal used
        cnt[0] += 1
        if cnt[0] > limit:
            raise Timeout
        L = len(order)
        if L == n:
            for i in range(n - r + 1, n):
                if not okw([order[(i + j) % n] for j in range(r)]):
                    return False
            if want_all:
                out.append(tuple(order))
                return False
            return True
        cands = [e for e in elems if not (used >> e) & 1]
        if rng is not None:
            rng.shuffle(cands)
        for e in cands:
            order.append(e)
            if okw(order[-r:] if L + 1 >= r else order):
                used |= 1 << e
                if dfs():
                    return True
                used &= ~(1 << e)
            order.pop()
        return False

    res = dfs()
    if want_all:
        return out
    return tuple(order) if res else None
