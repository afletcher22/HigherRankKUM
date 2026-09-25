"""Non-contiguous extension of a deletion CBO.

Given a rank-4 matroid (as a rank function on lists of items), a set S and a cyclic order sigma
of the other elements (a CBO of M-S), decide whether S can be interleaved into sigma (keeping
sigma's cyclic order) so that the result is a CBO of M.  Memoised DFS over
(sigma position, used part of S, last three entries, first three entries).
"""
from functools import lru_cache


def extend(rank, S, sigma, forbid_contiguous=False):
    """rank(list) -> int.  Returns an extended cyclic order, or None.
    forbid_contiguous: reject extensions in which all of S sits in one gap."""
    S = list(S)
    N = len(sigma)
    full = (1 << len(S)) - 1

    def ok_prefix(seq):
        return rank(seq) == len(seq)

    import sys
    sys.setrecursionlimit(10000)
    memo = set()

    def rec(seq, i, used):
        L = len(seq)
        if i == N and used == full:
            n = L
            for a in range(n - 3, n):
                if rank([seq[(a + j) % n] for j in range(4)]) != 4:
                    return None
            if forbid_contiguous:
                pos = [p for p, x in enumerate(seq) if isinstance(x, tuple)]
                gaps = {sum(1 for p2, y in enumerate(seq[:p]) if not isinstance(y, tuple)) for p in pos}
                if len(gaps) == 1:
                    return None
            return list(seq)
        key = (i, used, tuple(seq[-3:]), tuple(seq[:3]))
        if L >= 3 and key in memo:
            return None
        cands = []
        if i < N:
            cands.append((sigma[i], i + 1, used))
        for j in range(len(S)):
            if not used >> j & 1:
                cands.append((S[j], i, used | 1 << j))
        for c, i2, u2 in cands:
            w = seq[-3:] + [c]
            if (L >= 3 and rank(w) == 4) or (L < 3 and ok_prefix(seq + [c])):
                seq.append(c)
                r = rec(seq, i2, u2)
                seq.pop()
                if r is not None:
                    return r
        if L >= 3 and not forbid_contiguous:
            memo.add(key)
        return None

    return rec([sigma[0]], 1, 0)
