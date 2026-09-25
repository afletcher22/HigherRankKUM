"""(G) 3k-plane gluing experiments.

M strict rank-4 on 4k+2, H a rank-3 flat with |H|=3k, R=E-H (|R|=k+2).

Schedule S00 ("two adjacent R-pairs"):
   [r1 r2] (HHH r)^(m1-1) HHH [r3 r4] (HHH r)^(m2-1) HHH ,  m1+m2=k, m1,m2>=1
The only windows with >=2 R's are, around each adjacent pair P placed at cut c of the
H-order tau (between tau[c-1] and tau[c]):
   P+{tau[c-2],tau[c-1]},  P+{tau[c-1],tau[c]},  P+{tau[c],tau[c+1]}.
All other windows are 3H+1R with a consecutive tau-triple, automatic when that triple
is a basis of M|H (H is a flat).  Cuts must satisfy c2-c1 = 0 mod 3, c1 != c2.
"""
import itertools, random, sys, time
from kum import *


def good_cuts(M, tau, P):
    m = len(tau)
    p0, p1 = P
    out = set()
    for c in range(m):
        a, b, cc, d = tau[(c - 2) % m], tau[(c - 1) % m], tau[c], tau[(c + 1) % m]
        if M.is_basis([p0, p1, a, b]) and M.is_basis([p0, p1, b, cc]) and M.is_basis([p0, p1, cc, d]):
            out.add(c)
    return out


def rank3_cbos(M, Hl, limit=10 ** 6, cap=None, rng=None):
    """all rank-3 CBOs of M|H with Hl[0] first (rotation fixed, reflections kept)."""
    if cap is None:
        return find_cbo(M, elems=Hl, r=3, first=Hl[0], limit=limit, want_all=True)
    out = set()
    tries = 0
    while len(out) < cap and tries < 4 * cap:
        tries += 1
        o = find_cbo(M, elems=Hl, r=3, first=Hl[0], limit=limit, rng=rng)
        if o is None:
            break
        out.add(o)
    return sorted(out)


def s00_for_tau(M, tau, R):
    """return a witness (P1,c1,P2,c2) or None"""
    m = len(tau)
    pairs = [P for P in itertools.combinations(R, 2) if M.rk(P) == 2]
    gc = {P: good_cuts(M, tau, P) for P in pairs}
    for P1 in pairs:
        if not gc[P1]:
            continue
        for P2 in pairs:
            if set(P1) & set(P2) or not gc[P2]:
                continue
            for c1 in gc[P1]:
                for c2 in gc[P2]:
                    if c1 != c2 and (c2 - c1) % 3 == 0:
                        return (P1, c1, P2, c2)
    return None


def build_s00(tau, R, wit):
    P1, c1, P2, c2 = wit
    m = len(tau)
    rest = [x for x in R if x not in P1 and x not in P2]
    # rotate tau so c1 = 0
    t = [tau[(c1 + i) % m] for i in range(m)]
    d = (c2 - c1) % m
    order = list(P1)
    seg1 = t[:d]
    seg2 = t[d:]
    ri = iter(rest)
    for i in range(0, len(seg1), 3):
        order += seg1[i:i + 3]
        if i + 3 < len(seg1):
            order.append(next(ri))
    order += list(P2)
    for i in range(0, len(seg2), 3):
        order += seg2[i:i + 3]
        if i + 3 < len(seg2):
            order.append(next(ri))
    return order


def fixed_skeleton(k):
    return (0, 0, 0, 1) * (k - 2) + (0, 0, 0, 1, 0, 1, 0, 0, 1, 1)


def repo_skeleton_for_tau(M, tau, R):
    """repo skeleton (HHHR)^(k-2) HHHR HR HH RR, all rotations of tau, all R orders."""
    m = len(tau)
    k = m // 3
    sk = fixed_skeleton(k)
    for rot in range(m):
        t = tau[rot:] + tau[:rot]
        for ro in itertools.permutations(R):
            hi = ri = 0
            o = []
            for b in sk:
                if b == 0:
                    o.append(t[hi]); hi += 1
                else:
                    o.append(ro[ri]); ri += 1
            if is_cbo(M, o):
                return o
    return None


def extend_tau_any(M, tau, R, limit=10 ** 6):
    """exists CBO of M whose induced cyclic order on H is tau (any R placement)."""
    n = len(tau) + len(R)
    order = [tau[0]]
    st = {"ti": 1, "used": 0, "cnt": 0}

    def ok():
        if len(order) >= 4:
            return M.rk(order[-4:]) == 4 and len(set(order[-4:])) == 4
        return M.rk(order) == len(order)

    def dfs():
        st["cnt"] += 1
        if st["cnt"] > limit:
            raise Timeout
        if len(order) == n:
            return all(M.is_basis([order[(i + j) % n] for j in range(4)]) for i in range(n - 3, n))
        if st["ti"] < len(tau):
            order.append(tau[st["ti"]]); st["ti"] += 1
            if ok() and dfs():
                return True
            st["ti"] -= 1; order.pop()
        for c in R:
            if (st["used"] >> c) & 1:
                continue
            order.append(c); st["used"] |= 1 << c
            if ok() and dfs():
                return True
            st["used"] &= ~(1 << c); order.pop()
        return False
    return list(order) if dfs() else None


def analyse(M, H, tau_cap=None, rng=None, do_repo=False, do_every=False):
    Hl = bits(H)
    R = [x for x in range(M.n) if not (H >> x) & 1]
    taus = rank3_cbos(M, Hl, cap=tau_cap, rng=rng)
    res = dict(ntau=len(taus), s00_tau=0, repo_tau=0, every_fail=0)
    for tau in taus:
        tau = list(tau)
        w = s00_for_tau(M, tau, R)
        if w:
            o = build_s00(tau, R, w)
            assert is_cbo(M, o), (tau, w, o)
            res["s00_tau"] += 1
        if do_repo and repo_skeleton_for_tau(M, tau, R):
            res["repo_tau"] += 1
        if do_every:
            try:
                if extend_tau_any(M, tau, R) is None:
                    res["every_fail"] += 1
            except Timeout:
                pass
    return res
