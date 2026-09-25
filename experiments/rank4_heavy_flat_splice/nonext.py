"""Adversarial search for deletion CBOs that admit NO extension (Conjecture E).

Matroid M (kum.Mat, elements are indices), basis S, and Y = E - S.  DFS over cyclic orders sigma
of Y that are CBOs of M-S.  A prefix is pruned as soon as S can be interleaved into its interior
(at least three sigma-entries before the first S-entry and after the last one), since such an
interleaving survives every completion.  This is tracked by a forward state set of
(used part of S, last three merged entries, trailing sigma-entries since the last S-entry, max 3).
Complete orders are then tested cyclically with ext.extend.
"""
from ext import extend
from kum import Timeout


def _close(rank, S, states):
    """Allow any number of S-elements to follow each state."""
    full = (1 << len(S)) - 1
    out = set(states)
    stack = list(states)
    while stack:
        used, last3, tail = stack.pop()
        if used == full or len(last3) < 3:
            continue
        for j, s in enumerate(S):
            if used >> j & 1:
                continue
            w = list(last3) + [s]
            if rank(w) == 4:
                st = (used | 1 << j, tuple(w[-3:]), 0)
                if st not in out:
                    out.add(st)
                    stack.append(st)
    return out


def advance(rank, S, states, y, allow_S=True):
    nxt = set()
    for used, last3, tail in states:
        w = list(last3) + [y]
        if rank(w) == len(w):
            nxt.add((used, tuple(w[-3:]), min(tail + 1, 3)))
    return _close(rank, S, nxt) if allow_S else nxt


def done(states, full):
    return any(u == full and t >= 3 for u, _, t in states)


def nonext_orders(M, S, limit=10 ** 6, want=1, rng=None):
    rank = M.rk
    S = list(S)
    full = (1 << len(S)) - 1
    Y = [x for x in range(M.n) if x not in S]
    n = len(Y)
    order = [Y[0]]
    used = {Y[0]}
    found = []
    cnt = [0]
    stack_states = [{(0, (Y[0],), 1)}]

    def dfs():
        cnt[0] += 1
        if cnt[0] > limit:
            raise Timeout
        L = len(order)
        if L == n:
            for i in range(n - 3, n):
                if rank([order[(i + j) % n] for j in range(4)]) != 4:
                    return False
            if extend(rank, S, list(order)) is None:
                found.append(list(order))
                return len(found) >= want
            return False
        cands = [e for e in Y if e not in used]
        if rng:
            rng.shuffle(cands)
        for e in cands:
            order.append(e)
            if rank(order[-4:]) == min(4, L + 1):
                nst = advance(rank, S, stack_states[-1], e, allow_S=(L + 1 >= 3))
                if not done(nst, full):
                    used.add(e)
                    stack_states.append(nst)
                    if dfs():
                        return True
                    stack_states.pop()
                    used.discard(e)
            order.pop()
        return False

    try:
        dfs()
    except Timeout:
        return found, "timeout", cnt[0]
    return found, "exhausted", cnt[0]
