"""Block-splice lemma (BSL) for the 3k-plane endpoint.

M rank 4, K a rank-3 flat, T subset K a basis of K, c outside K,
sigma' a CBO of M' = M - (T + c).  If sigma' has a K-run of length exactly 3
whose neighbouring runs are nonempty, the universal rank-3 two-gap theorem
splices T into that run, and c is placed after the third K of the new 6-run.
"""
import itertools
from kum import *


def uniformly_dense_rank4(M, ground):
    """exact check: |X| * 4 <= |ground| * r(X) over flats of M|ground (ranks 1..3), rank 4."""
    n = pc(ground)
    if M.r(ground) != 4:
        return False
    fl = M.flats(ground)
    for j in (1, 2, 3):
        for F in fl[j]:
            if 4 * pc(F) > n * j:
                return False
    return True


def hitting_sets(M, K):
    """all D = T+{c}, T basis of M|K, c outside K, with M-D uniformly dense."""
    Kl = bits(K)
    C = [x for x in range(M.n) if not (K >> x) & 1]
    out = []
    for T in itertools.combinations(Kl, 3):
        if M.rk(T) != 3:
            continue
        for c in C:
            D = sum(1 << x for x in T) | (1 << c)
            if uniformly_dense_rank4(M, M.full & ~D):
                out.append((T, c))
    return out


def two_gap(M, T, p, a, b, c, q):
    """return ('first'|'second', order of T) per the Rank3KUM two-gap statement."""
    for d in itertools.permutations(T):
        if (M.rk([p, a, d[0]]) == 3 and M.rk([a, d[0], d[1]]) == 3 and
                M.rk([d[1], d[2], b]) == 3 and M.rk([d[2], b, c]) == 3):
            return ("first", d)
    for d in itertools.permutations(T):
        if (M.rk([a, b, d[0]]) == 3 and M.rk([b, d[0], d[1]]) == 3 and
                M.rk([d[1], d[2], c]) == 3 and M.rk([d[2], c, q]) == 3):
            return ("second", d)
    return None


def usable_runs(sigma, K):
    """indices i (position of first K of a 3-run) with nonempty neighbouring runs."""
    n = len(sigma)
    isK = [(K >> x) & 1 for x in sigma]
    out = []
    for i in range(n):
        # run of exactly 3 K's at i..i+2, bounded by C at i-1 and i+3, and K at i-2 and i+4
        if (isK[i] and isK[(i + 1) % n] and isK[(i + 2) % n] and not isK[(i - 1) % n]
                and not isK[(i + 3) % n] and isK[(i - 2) % n] and isK[(i + 4) % n]):
            out.append(i)
    return out


def splice(M, K, T, c, sigma):
    """apply BSL; return a CBO of M or None (if no usable run)."""
    n = len(sigma)
    runs = usable_runs(sigma, K)
    for i in runs:
        w = sigma[(i - 2) % n]
        x1, x2, x3 = sigma[i], sigma[(i + 1) % n], sigma[(i + 2) % n]
        y = sigma[(i + 4) % n]
        g = two_gap(M, T, w, x1, x2, x3, y)
        if g is None:
            raise AssertionError("two-gap theorem violated?!")
        kind, d = g
        if kind == "first":
            block = [x1, d[0], d[1], c, d[2], x2, x3]
        else:
            block = [x1, x2, d[0], c, d[1], d[2], x3]
        # rotate so run starts at 0, replace
        rot = [sigma[(i + j) % n] for j in range(n)]
        new = block + rot[3:]
        return new
    return None
