"""Search-based choice for the decomposition principle with a 10-element base.

Given flat F of rank rho with |F| = rho*(k+1/2) - s, find E0 (|E0|=10) such that
  * M|E0 is uniformly dense, plus extra base conditions (no 7-plane / no 5-line) where the
    corresponding SAT base lemma needs them;
  * N_F = M|F (+) M/F restricted to E-E0 partitions into k-2 bases, i.e.
      F-F0 partitions into bases of M|F and X-X0 into bases of M/F (rank 4-rho).
The search uses a near-partition: leftovers + two blocks, then random restarts.
Also returns the DP-constructed CBO (verified) when successful.
"""
import itertools, random
from kum import *
from bsl import uniformly_dense_rank4
from hfs import splice_hfs, Contract
from theorem_pl import site_cbo_rho


def partition_blocks(R, S, size):
    """partition S into blocks of `size` elements each of rank `size` in oracle R (backtracking)."""
    S = list(S)
    if not S:
        return []
    a = S[0]
    for rest in itertools.combinations(S[1:], size - 1):
        blk = (a,) + rest
        if R.rk(list(blk)) == size:
            rem = [x for x in S if x not in blk]
            sub = partition_blocks(R, rem, size)
            if sub is not None:
                return [blk] + sub
    return None


def base_ok(M, E0, strict_planes, strict_lines):
    m = sum(1 << x for x in E0)
    if not uniformly_dense_rank4(M, m):
        return False
    fl = M.flats(m)
    if strict_planes and any(pc(F) >= 7 for F in fl[3]):
        return False
    if strict_lines and any(pc(F) >= 5 for F in fl[2]):
        return False
    return True


class RestrictOracle:
    def __init__(self, M):
        self.M = M

    def rk(self, L):
        return self.M.rk(L)


def dp_general(M, F, rng, strict_planes=False, strict_lines=False, tries=3000):
    rho = M.r(F)
    Fl = bits(F)
    X = [x for x in range(M.n) if not (F >> x) & 1]
    k = (M.n - 2) // 4
    f0 = len(Fl) - rho * (k - 2)
    x0 = len(X) - (4 - rho) * (k - 2)
    RF = RestrictOracle(M)
    RX = Contract(M, F)
    for _ in range(tries):
        F0 = rng.sample(Fl, f0)
        X0 = rng.sample(X, x0)
        E0 = F0 + X0
        if not base_ok(M, E0, strict_planes, strict_lines):
            continue
        TF = partition_blocks(RF, [x for x in Fl if x not in F0], rho) if rho > 1 else \
            [(x,) for x in Fl if x not in F0]
        if TF is None:
            continue
        TX = partition_blocks(RX, [x for x in X if x not in X0], 4 - rho) if 4 - rho > 1 else \
            [(x,) for x in X if x not in X0]
        if TX is None:
            continue
        s0 = site_cbo_rho(M, E0, F, rho)
        if not isinstance(s0, list):
            return None, ("BASE LEMMA FAILED?!", E0)
        sigma = s0
        for tf, tx in zip(TF, TX):
            sigma, _ = splice_hfs(M, F, list(tf), list(tx), sigma)
            assert sigma is not None
        assert is_cbo(M, sigma) and sorted(sigma) == list(range(M.n))
        return sigma, "ok"
    return None, "no choice found"
