"""Chains of bases: serial-exchange relations and closed walks, for any basis oracle.

A chain is a cyclic sequence of bases B_0, ..., B_{k-1} of a rank-r matroid.  An *interval
ordering* orders each basis so that the concatenation is a cyclic basis ordering; equivalently
(order of B_i, order of B_{i+1}) is a serial exchange for every i: every suffix of B_i together
with the complementary prefix of B_{i+1} is a basis.
"""
import itertools
import numpy as np


class Ctx:
    def __init__(self, r):
        self.r = r
        self.perms = list(itertools.permutations(range(r)))
        self.subsets = {t: list(itertools.combinations(range(r), t)) for t in range(r + 1)}
        sidx = {t: {frozenset(s): i for i, s in enumerate(self.subsets[t])} for t in range(r + 1)}
        self.SUF = {t: np.array([sidx[r - t][frozenset(p[t:])] for p in self.perms]) for t in range(1, r)}
        self.PRE = {t: np.array([sidx[t][frozenset(p[:t])] for p in self.perms]) for t in range(1, r)}
        self.PREF_MASK = np.array([[sum(1 << x for x in p[:c]) for c in range(r + 1)] for p in self.perms])

    def rel(self, B, Bn, is_basis):
        """Serial exchange relation B -> Bn: boolean matrix indexed by (order of B, order of Bn)."""
        r = self.r
        R = np.ones((len(self.perms), len(self.perms)), dtype=bool)
        for t in range(1, r):
            tab = np.zeros((len(self.subsets[r - t]), len(self.subsets[t])), dtype=bool)
            for i, U in enumerate(self.subsets[r - t]):
                u = [B[x] for x in U]
                for j, V in enumerate(self.subsets[t]):
                    tab[i, j] = is_basis(u + [Bn[x] for x in V])
            R &= tab[self.SUF[t]][:, self.PRE[t]]
        return R

    def closed(self, rels, i=0):
        """Orders of basis i lying on a closed walk through the cyclic list of relations."""
        k = len(rels)
        P = rels[i]
        for j in range(1, k):
            P = mm(P, rels[(i + j) % k])
        return P.diagonal()

    def prefix_free(self, ok):
        """Every subset of the basis is an initial segment of some allowed order."""
        if not ok.any():
            return False
        return len(np.unique(self.PREF_MASK[ok])) == (1 << self.r)


def mm(A, B):
    return (A.astype(np.uint16) @ B.astype(np.uint16)) > 0


def gf2_rank(vs):
    basis = []
    for v in vs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)


def gf2_is_basis(r):
    return lambda vs: len(set(vs)) == r and gf2_rank(vs) == r


def analyse(ctx, bases, is_basis):
    """bases: list of k tuples.  Returns (some ordering exists, prefix freedom) over both
    cyclic orientations (for k = 2 there is only one)."""
    k = len(bases)
    orders = [list(range(k))] if k == 2 else [list(range(k)), [0] + list(range(k - 1, 0, -1))]
    anyv, pf = True, True
    for o in orders:
        seq = [bases[i] for i in o]
        rels = [ctx.rel(seq[i], seq[(i + 1) % k], is_basis) for i in range(k)]
        for i in range(k):
            ok = ctx.closed(rels, i)
            anyv = anyv and bool(ok.any())
            pf = pf and ctx.prefix_free(ok)
    return anyv, pf
