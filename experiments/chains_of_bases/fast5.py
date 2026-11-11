"""Fast GF(2) chain-of-bases tests (vectorised relations).

Mode r10 : fixed R10 pair (B1, B2), every third basis S of GF(2)^5 (83,328 of them).
Mode rand: random triples of bases of GF(2)^5.
Per instance, for the three bases in both cyclic orders:
  any     : some interval cyclic basis ordering exists
  frozen  : some Gabow ordering of (B1, B2) extends by inserting S contiguously
  PF      : every subset of every basis is an initial segment in some solution
"""
import itertools, random, sys, time
import numpy as np

r = 5
perms = list(itertools.permutations(range(r)))
NP = len(perms)
subsets = {t: list(itertools.combinations(range(r), t)) for t in range(r + 1)}
sidx = {t: {frozenset(s): i for i, s in enumerate(subsets[t])} for t in range(r + 1)}
# index arrays: for each perm and t, index of suffix set (size r-t) and prefix set (size t)
SUF = {t: np.array([sidx[r - t][frozenset(p[t:])] for p in perms]) for t in range(1, r)}
PRE = {t: np.array([sidx[t][frozenset(p[:t])] for p in perms]) for t in range(1, r)}
PREF_MASK = np.array([[sum(1 << x for x in p[:c]) for c in range(r + 1)] for p in perms])

def rank2(vs):
    basis = []
    for v in vs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)

def is_basis(vs):
    return len(set(vs)) == r and rank2(vs) == r

def rel(B, Bn):
    """serial exchange relation B -> Bn as an NP x NP boolean matrix"""
    R = np.ones((NP, NP), dtype=bool)
    for t in range(1, r):
        tab = np.zeros((len(subsets[r - t]), len(subsets[t])), dtype=bool)
        for i, U in enumerate(subsets[r - t]):
            u = [B[x] for x in U]
            for j, V in enumerate(subsets[t]):
                tab[i, j] = is_basis(u + [Bn[x] for x in V])
        R &= tab[SUF[t]][:, PRE[t]]
    return R

def mm(A, B):
    return (A.astype(np.uint16) @ B.astype(np.uint16)) > 0

def pf_ok(ok):
    got = set(np.unique(PREF_MASK[ok]).tolist()) if ok.any() else set()
    return len(got) == (1 << r)

def study(B1, B2, S, R12=None, R21=None):
    if R12 is None:
        R12, R21 = rel(B1, B2), rel(B2, B1)
    R1S, RS1, R2S, RS2 = rel(B1, S), rel(S, B1), rel(B2, S), rel(S, B2)
    G = R12 & R21.T
    E21 = mm(R2S, RS1).T
    E12 = mm(R1S, RS2)
    frozen = bool((G & (E21 | E12)).any())
    out = {'frozen': frozen}
    anyv = False; pf = True
    for chain in ([R12, R2S, RS1], [R1S, RS2, R21]):
        for i in range(3):
            P = chain[i]
            for j in range(1, 3):
                P = mm(P, chain[(i + j) % 3])
            ok = P.diagonal()
            anyv = anyv or bool(ok.any())
            pf = pf and pf_ok(ok)
    out['any'] = anyv; out['pf'] = pf
    return out

def all_bases():
    return [c for c in itertools.combinations(range(1, 1 << r), r) if rank2(c) == r]

def main():
    mode = sys.argv[1]; limit = int(sys.argv[2]); t0 = time.time()
    tot = 0; bad = {'any': 0, 'frozen': 0, 'pf': 0}; ex = {'any': [], 'frozen': [], 'pf': []}
    if mode == 'r10':
        circ = ['11001', '11100', '01110', '00111', '10011']
        B1 = tuple(1 << i for i in range(5))
        B2 = tuple(sum(int(circ[i][j]) << i for i in range(5)) for j in range(5))
        assert is_basis(list(B1)) and is_basis(list(B2))
        R12, R21 = rel(B1, B2), rel(B2, B1)
        bases = all_bases()
        random.Random(5).shuffle(bases)
        gen = ((B1, B2, S, R12, R21) for S in bases[:limit])
    else:
        rng = random.Random(9)
        def rb():
            while True:
                B = tuple(rng.randrange(1, 32) for _ in range(5))
                if is_basis(list(B)):
                    return B
        gen = ((rb(), rb(), rb(), None, None) for _ in range(limit))
    for B1_, B2_, S, a, b in gen:
        res = study(B1_, B2_, S, a, b)
        tot += 1
        for k in bad:
            if not res[k]:
                bad[k] += 1
                if len(ex[k]) < 3:
                    ex[k].append((B1_, B2_, S))
        if tot % 5000 == 0:
            print("  ...", tot, bad, "%.0fs" % (time.time() - t0), flush=True)
    print("mode %s: %d instances; no ordering at all: %d; no frozen extension: %d; PF fails: %d  (%.0fs)" % (
        mode, tot, bad['any'], bad['frozen'], bad['pf'], time.time() - t0))
    for k in ex:
        for e in ex[k]:
            print("   example failing", k, e)

main()
