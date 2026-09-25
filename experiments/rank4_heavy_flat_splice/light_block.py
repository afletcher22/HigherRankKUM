"""Adversarial search for fully blocked contiguous basis splices (B, sigma').

sigma' is a CBO of M-B such that for EVERY gap and EVERY order of B, contiguous insertion
fails.  DFS over sigma' with pruning: as soon as a gap's six neighbours are fixed and the gap
works, the branch dies.
"""
import itertools, random
from kum import *


def gap_works(M, B, L3, R3):
    for pi in itertools.permutations(B):
        seq = list(L3) + list(pi) + list(R3)
        if all(M.rk(seq[i:i + 4]) == 4 for i in range(len(seq) - 3)):
            return True
    return False


def blocked_orders(M, B, limit=2 * 10 ** 6, want=1, rng=None):
    els = [x for x in range(M.n) if x not in B]
    n = len(els)
    first = els[0]
    order = [first]
    used = {first}
    found = []
    cnt = [0]

    def okw(w):
        return M.rk(w) == len(w)

    def dfs():
        cnt[0] += 1
        if cnt[0] > limit:
            raise Timeout
        L = len(order)
        if L == n:
            for i in range(n - 3, n):
                if not okw([order[(i + j) % n] for j in range(4)]):
                    return False
            # remaining gaps (involving wrap-around)
            for g in range(n):
                if g >= 3 and g <= n - 3:
                    continue
                if gap_works(M, B, [order[(g - 3 + t) % n] for t in range(3)],
                             [order[(g + t) % n] for t in range(3)]):
                    return False
            found.append(list(order))
            return len(found) >= want
        cands = [e for e in els if e not in used]
        if rng:
            rng.shuffle(cands)
        for e in cands:
            order.append(e)
            if okw(order[-4:] if L + 1 >= 4 else order):
                # gap between positions L-3 and L-2 now has 3 left and 3 right fixed
                ok = True
                if L + 1 >= 6:
                    g = L - 2
                    if gap_works(M, B, order[g - 3:g], order[g:g + 3]):
                        ok = False
                if ok:
                    used.add(e)
                    if dfs():
                        return True
                    used.discard(e)
            order.pop()
        return False
    try:
        dfs()
    except Timeout:
        return found, "timeout"
    return found, "exhausted"
