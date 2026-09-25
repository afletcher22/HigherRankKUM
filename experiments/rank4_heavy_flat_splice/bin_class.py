"""Enumerate binary rank-4 multisets on n=4k+2 (labelled parallel copies) that are strict
with given caps, via PG(3,2) lines/planes."""
import itertools
from kum import gf2_rank

PTS = list(range(1, 16))
LINES = sorted({frozenset((a, b, a ^ b)) for a in PTS for b in PTS if a < b})
PLANES = sorted({frozenset(x for x in PTS if bin(x & f).count("1") % 2 == 0) for f in PTS})
assert len(LINES) == 35 and len(PLANES) == 15


def caps_ok(cnt, k, t0=True):
    if max(cnt.values()) > k:
        return False
    for L in LINES:
        if sum(cnt.get(x, 0) for x in L) > 2 * k:
            return False
    cap3 = 3 * k if t0 else 3 * k + 1
    for P in PLANES:
        if sum(cnt.get(x, 0) for x in P) > cap3:
            return False
    return True


def multisets(n, k, t0=True):
    """all multiplicity vectors over 15 points summing to n with caps; rank 4."""
    out = []
    def rec(i, rem, cur):
        if i == 15:
            if rem == 0:
                cnt = {PTS[j]: cur[j] for j in range(15) if cur[j]}
                if gf2_rank(list(cnt)) == 4 and caps_ok(cnt, k, t0):
                    out.append(dict(cnt))
            return
        for c in range(0, min(k, rem) + 1):
            cur.append(c)
            rec(i + 1, rem - c, cur)
            cur.pop()
    rec(0, n, [])
    return out


def cols_of(cnt):
    cols = []
    for v in sorted(cnt):
        cols += [v] * cnt[v]
    return tuple(cols)


# GL(4,2) canonical form (for orbit reduction)
def _gl42():
    mats = []
    for cols in itertools.permutations(PTS, 4):
        if gf2_rank(list(cols)) == 4:
            mats.append(cols)
    return mats


_GL = None


def apply(Mc, v):
    out = 0
    for i in range(4):
        if (v >> i) & 1:
            out ^= Mc[i]
    return out


def canon(cnt):
    global _GL
    if _GL is None:
        _GL = _gl42()
    best = None
    items = list(cnt.items())
    for Mc in _GL:
        key = tuple(sorted((apply(Mc, v), c) for v, c in items))
        if best is None or key < best:
            best = key
    return best
