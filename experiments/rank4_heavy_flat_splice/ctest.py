"""(C*) completion test: K a 3k-plane of M, e outside K, sigma a CBO of M\\e.
Question: is there a CBO of M whose induced cyclic order on K equals the inherited
order tau of sigma (all rephasings / complement placements / labels allowed)?
"""
import itertools, random, time
from kum import *
from gtest import extend_tau_any


def inherited(sigma, K):
    return [x for x in sigma if (K >> x) & 1]


def bad_triples(M, tau):
    m = len(tau)
    return [i for i in range(m) if M.rk([tau[(i + j) % m] for j in range(3)]) < 3]


def gap_type(sigma, K):
    n = len(sigma)
    Rpos = [i for i in range(n) if not (K >> sigma[i]) & 1]
    gaps = [((Rpos[(j + 1) % len(Rpos)] - Rpos[j]) % n) - 1 for j in range(len(Rpos))]
    return tuple(sorted((3 - g for g in gaps if g < 3), reverse=True))


def deletion_cbos(M, e, limit=10 ** 7, sample=None, rng=None):
    els = [x for x in range(M.n) if x != e]
    if sample is None:
        return find_cbo(M, elems=els, first=els[0], limit=limit, want_all=True)
    out = set()
    tries = 0
    while len(out) < sample and tries < 5 * sample:
        tries += 1
        try:
            o = find_cbo(M, elems=els, first=els[0], limit=limit, rng=rng)
        except Timeout:
            continue
        if o is None:
            break
        out.add(o)
    return sorted(out)


def completes(M, K, sigma, limit=10 ** 6):
    tau = inherited(sigma, K)
    C = [x for x in range(M.n) if not (K >> x) & 1]
    return extend_tau_any(M, tau, C, limit=limit)
