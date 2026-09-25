"""Decomposition-principle pipelines for a heavy point (k-point) and a heavy line (2k-line).

Point P (|P|=k): base M0 = P0 ∪ X0 with |P0|=2, |X0|=8; remaining X-X0 partitioned into
  bases Z_i of M/P (rank 3), each paired with an element of P-P0 (Theorem 4, rho=1).
Line L (|L|=2k): base M0 = L0 ∪ X0 with |L0|=4, |X0|=6; L-L0 partitioned into independent
  pairs, X-X0 into bases of M/L (rank 2), paired up (Theorem 4, rho=2).
Base lemmas (10 elements) are SAT-proved in base_sat_general.py (rho=1 f=2; rho=2 f=4).
Here the base is chosen by search and its site-CBO is found by DFS.
"""
import itertools, random
from kum import *
from bsl import uniformly_dense_rank4
from hfs import splice_hfs, Contract


def partition_pairs(R, S):
    """partition list S into pairs independent in rank-oracle R (rank-2 partition); backtracking."""
    S = list(S)
    if not S:
        return []
    a = S[0]
    for b in S[1:]:
        if R.rk([a, b]) == 2:
            rest = [x for x in S if x not in (a, b)]
            sub = partition_pairs(R, rest)
            if sub is not None:
                return [(a, b)] + sub
    return None


def partition_triples(R, S):
    S = list(S)
    if not S:
        return []
    a = S[0]
    for b, c in itertools.combinations(S[1:], 2):
        if R.rk([a, b, c]) == 3:
            rest = [x for x in S if x not in (a, b, c)]
            sub = partition_triples(R, rest)
            if sub is not None:
                return [(a, b, c)] + sub
    return None


def site_positions_ok(o, F, rho):
    n = len(o)
    f = "".join(str((F >> x) & 1) for x in o)
    s = f + f
    pats = {3: ["1011101"], 1: ["0100010"], 2: ["100110", "011001", "010101", "101010"]}[rho]
    return any(p in s for p in pats)


def site_cbo_rho(M, E0, F, rho, limit=10 ** 7):
    from dp import _cbo_iter
    try:
        for o in _cbo_iter(M, list(E0), limit):
            if site_positions_ok(o, F, rho):
                return list(o)
    except Timeout:
        return "timeout"
    return None


def dp_point(M, P, rng, tries=4000):
    k = (M.n - 2) // 4
    Pl = bits(P)
    X = [x for x in range(M.n) if not (P >> x) & 1]
    R = Contract(M, P)
    for _ in range(tries):
        X0 = rng.sample(X, 8)
        P0 = Pl[:2]
        E0 = P0 + X0
        if not uniformly_dense_rank4(M, sum(1 << x for x in E0)):
            continue
        rest = [x for x in X if x not in X0]
        Z = partition_triples(R, rest)
        if Z is None:
            continue
        s0 = site_cbo_rho(M, E0, P, 1)
        if not isinstance(s0, list):
            return None, "base failed?!"
        sigma = s0
        for p, z in zip(Pl[2:], Z):
            sigma, _ = splice_hfs(M, P, [p], list(z), sigma)
        assert is_cbo(M, sigma) and sorted(sigma) == list(range(M.n))
        return sigma, "ok"
    return None, "no choice found"


def dp_line(M, L, rng, tries=4000):
    k = (M.n - 2) // 4
    Ll = bits(L)
    X = [x for x in range(M.n) if not (L >> x) & 1]
    R = Contract(M, L)
    for _ in range(tries):
        L0 = rng.sample(Ll, 4)
        X0 = rng.sample(X, 6)
        E0 = L0 + X0
        if not uniformly_dense_rank4(M, sum(1 << x for x in E0)):
            continue
        LP = partition_pairs(M, [x for x in Ll if x not in L0])
        XP = partition_pairs(R, [x for x in X if x not in X0])
        if LP is None or XP is None:
            continue
        s0 = site_cbo_rho(M, E0, L, 2)
        if not isinstance(s0, list):
            return None, "base failed?!"
        sigma = s0
        for lp, xp in zip(LP, XP):
            sigma, _ = splice_hfs(M, L, list(lp), list(xp), sigma)
        assert is_cbo(M, sigma) and sorted(sigma) == list(range(M.n))
        return sigma, "ok"
    return None, "no choice found"
