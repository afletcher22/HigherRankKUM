"""Shared combinatorics for the independent Claim A / Claim B check.

Element ids: S = {0,1,2,3}; e_i has id 4+i.  Subsets are bitmasks.
"""
from itertools import combinations, permutations

S_IDS = (0, 1, 2, 3)
S_MASK = 0b1111


def eid(i):
    return 4 + i


def mask(it):
    m = 0
    for x in it:
        m |= 1 << x
    return m


def popcount(m):
    return bin(m).count("1")


# ---------------------------------------------------------------- linear (Claim A)

def linear_interleavings(L):
    """Method 1: choose the 4 slots of S inside the free middle part, then an order of S.

    Condition (a): e_0,e_1,e_2 come before every S element and e_{L-3..L-1} after,
    i.e. S lives in gaps 3..L-3 of the e-sequence; any number per gap, any order.
    """
    E = [eid(i) for i in range(L)]
    head, mid, tail = E[:3], E[3:L - 3], E[L - 3:]
    m = len(mid) + 4
    for pos in combinations(range(m), 4):
        ps = set(pos)
        for perm in permutations(S_IDS):
            out, im, is_ = [], iter(mid), iter(perm)
            for j in range(m):
                out.append(next(is_) if j in ps else next(im))
            yield tuple(head + out + tail)


def linear_interleavings_insert(L):
    """Method 2 (independent): insert s0,s1,s2,s3 one at a time at every legal position.

    A position is legal iff the number of e's before it lies in [3, L-3].
    Each final sequence arises exactly once (labels are inserted in a fixed order).
    """
    base = [eid(i) for i in range(L)]
    out = []

    def rec(seq, k):
        if k == 4:
            out.append(tuple(seq))
            return
        ecount = 0
        for p in range(len(seq) + 1):
            if p > 0 and seq[p - 1] >= 4:
                ecount += 1
            if 3 <= ecount <= L - 3:
                rec(seq[:p] + [k] + seq[p:], k + 1)

    rec(base, 0)
    return out


def linear_windows(seq):
    return [mask(seq[j:j + 4]) for j in range(len(seq) - 3)]


def linear_forced(L):
    """Hypothesis bases: S and every 4 consecutive e's."""
    return [S_MASK] + [mask(eid(i + t) for t in range(4)) for i in range(L - 3)]


def linear_blocks(L):
    """Blocks S u {e_i..e_{i+3}}: every window of every interleaving lies in one."""
    return [S_MASK | mask(eid(i + t) for t in range(4)) for i in range(L - 3)]


# ---------------------------------------------------------------- cyclic (Claim B)

def cyclic_interleavings(N):
    """Method 1: read the merged cycle starting at e_0; the rest is a linear shuffle of
    e_1..e_{N-1} with an ordering of S (S elements after e_{N-1} sit in gap 0)."""
    rest = [eid(i) for i in range(1, N)]
    m = len(rest) + 4
    for pos in combinations(range(m), 4):
        ps = set(pos)
        for perm in permutations(S_IDS):
            out, ir, is_ = [], iter(rest), iter(perm)
            for j in range(m):
                out.append(next(is_) if j in ps else next(ir))
            yield tuple([eid(0)] + out)


def canon_cyclic(seq):
    k = seq.index(eid(0))
    return tuple(seq[k:] + seq[:k])


def cyclic_interleavings_insert(N):
    """Method 2 (independent): insert s0..s3 one at a time into the cyclic list after any
    existing entry (len(seq) choices = number of cyclic gaps); canonicalise at e_0."""
    base = [eid(i) for i in range(N)]
    out = []

    def rec(seq, k):
        if k == 4:
            out.append(canon_cyclic(seq))
            return
        for p in range(1, len(seq) + 1):  # insert after seq[p-1]
            rec(seq[:p] + [k] + seq[p:], k + 1)

    rec(base, 0)
    return out


def cyclic_windows(seq):
    m = len(seq)
    return [mask(seq[(j + t) % m] for t in range(4)) for j in range(m)]


def cyclic_forced(N):
    return [S_MASK] + [mask(eid((i + t) % N) for t in range(4)) for i in range(N)]


def cyclic_blocks(N):
    return [S_MASK | mask(eid((i + t) % N) for t in range(4)) for i in range(N)]


# ---------------------------------------------------------------- instance data

def instance(kind, P):
    """Return (n, forced_bases, blocks, interleavings, clause_sets).

    clause_sets: deduplicated frozensets of window masks (forced bases removed), one per
    interleaving: 'some window of this interleaving is not a basis'.
    """
    if kind == "A":
        n = 4 + P
        inter = list(linear_interleavings(P))
        forced = linear_forced(P)
        blocks = linear_blocks(P)
        wins = linear_windows
    else:
        n = 4 + P
        inter = list(cyclic_interleavings(P))
        forced = cyclic_forced(P)
        blocks = cyclic_blocks(P)
        wins = cyclic_windows
    fset = set(forced)
    cs = set()
    for seq in inter:
        w = frozenset(x for x in wins(seq) if x not in fset)
        assert w, "interleaving with only hypothesis windows"
        cs.add(w)
    # soundness of the block relaxation: every window / hypothesis set inside a block
    allw = set(fset)
    for c in cs:
        allw |= c
    for w in allw:
        assert popcount(w) == 4
        assert any(w & ~B == 0 for B in blocks), "window not inside any block"
    return n, forced, blocks, inter, cs
