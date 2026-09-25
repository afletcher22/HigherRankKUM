"""Theorem G pipeline: strict t=0 rank-4 M on 4k+2 with a 3k-point plane K  ->  explicit CBO.

1. Edmonds: partition K into k bases D_1..D_k of M|K.
2. Choice lemma (paper proof, cases r(C)=4,3,2): pick D_a, D_b and C0 (|C0|=4) so that
   M0 = M|(D_a ∪ D_b ∪ C0) is uniformly dense.
3. Base lemma (SAT-proved in base_sat.py): M0 has a CBO with a K-site; found here by DFS.
4. Decomposition principle: splice D_i + c_i (Theorem 4, rho=3) for the remaining bases.
"""
import itertools
from kum import *
from bsl import uniformly_dense_rank4
from dp import partition_into_bases, site_cbo, splice_plane


def choose_base(M, K, blocks):
    Kset = set(bits(K))
    C = [x for x in range(M.n) if x not in Kset]
    Cm = sum(1 << x for x in C)
    rC = M.r(Cm)
    pts = lambda x: M.cl(1 << x)

    def pick_C0(noncollinear):
        # 4 elements of C, <=2 per point, and (if requested) rank >= 3
        for Q in itertools.combinations(C, 4):
            if any(sum(1 for y in Q if (pts(x) >> y) & 1) > 2 for x in Q):
                continue
            if noncollinear and M.rk(Q) < 3:
                continue
            if rC == 4 and M.rk(Q) < 4:
                continue
            return list(Q)
        return None

    if rC == 4:
        return blocks[0], blocks[1], pick_C0(True), "r4"
    if rC == 3:
        ell = M.cl(Cm) & K
        Da = next(D for D in blocks if sum(1 for x in D if (ell >> x) & 1) <= 1)
        Db = next(D for D in blocks if D != Da)
        return Da, Db, pick_C0(True), "r3"
    # rC == 2
    L = M.cl(Cm)
    P = L & K
    meets = lambda D: any((P >> x) & 1 for x in D)
    A = [D for D in blocks if not meets(D)]

    def heavy_planes(D):
        out = set()
        for x, y in itertools.combinations(D, 2):
            if M.r(L | 1 << x | 1 << y) == 3:          # x,y on a common plane through L
                out.add(M.cl(L | 1 << x) & K)
        return out
    for Da, Db in itertools.combinations(A, 2):
        if not (heavy_planes(Da) & heavy_planes(Db)):
            return Da, Db, pick_C0(False), "r2-avoid"
    for Da in A:
        for Db in blocks:
            if meets(Db) and not (heavy_planes(Da) & heavy_planes(Db)):
                return Da, Db, pick_C0(False), "r2-meet"
    return None


def theorem_g(M, K):
    k = pc(K) // 3
    blocks = partition_into_bases(M, K)
    assert blocks is not None, "Edmonds partition failed?!"
    ch = choose_base(M, K, blocks)
    assert ch is not None, "choice lemma failed"
    Da, Db, C0, case = ch
    E0 = list(Da) + list(Db) + C0
    assert uniformly_dense_rank4(M, sum(1 << x for x in E0)), ("M0 not dense", case)
    s0 = site_cbo(M, E0, K, limit=10 ** 7)
    assert isinstance(s0, list), ("base lemma failed?!", s0)
    rest_blocks = [D for D in blocks if D not in (Da, Db)]
    rest_c = [x for x in range(M.n) if not (K >> x) & 1 and x not in C0]
    sigma = s0
    for T, c in zip(rest_blocks, rest_c):
        sigma = splice_plane(M, K, T, c, sigma)
    assert is_cbo(M, sigma) and sorted(sigma) == list(range(M.n))
    return sigma, case
