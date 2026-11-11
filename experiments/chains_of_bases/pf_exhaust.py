"""Exhaustive tests over GF(2) of prefix freedom (PF) for chains of bases.

PF:  for every basis B_i of the chain and every T subset of B_i, some interval cyclic basis
     ordering has T as an initial segment of B_i.
PF2 (k = 2 only): every symmetric-exchange pair (T, T'), i.e. (A - T) + T' and (B - T') + T bases,
     is the pair of initial segments of some Gabow ordering.
Elements are vectors of GF(2)^r as ints; B_1 is the standard basis; repeated vectors are parallel.
"""
import itertools, sys, time
import numpy as np

def rank2(vs):
    basis = []
    for v in vs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)

def all_bases(r):
    pts = range(1, 1 << r)
    return [c for c in itertools.combinations(pts, r) if rank2(c) == r]

def perm_vec(v, p, r):
    w = 0
    for i in range(r):
        if v >> i & 1:
            w |= 1 << p[i]
    return w

def canon(Bs, r, cperms):
    best = None
    for p in cperms:
        key = tuple(tuple(sorted(perm_vec(v, p, r) for v in B)) for B in Bs)
        if best is None or key < best:
            best = key
    return best

def table(vecs, r):
    tab = set()
    for c in itertools.combinations(range(len(vecs)), r):
        vs = [vecs[i] for i in c]
        if len(set(vs)) == r and rank2(vs) == r:
            tab.add(sum(1 << i for i in c))
    return tab

def serial_rel(B, Bn, tab, perms, r):
    suf = [[sum(1 << B[x] for x in p[t:]) for t in range(1, r)] for p in perms]
    pre = [[sum(1 << Bn[x] for x in p[:t]) for t in range(1, r)] for p in perms]
    R = np.zeros((len(perms), len(perms)), dtype=bool)
    for i, s in enumerate(suf):
        for j, q in enumerate(pre):
            R[i, j] = all((s[t] | q[t]) in tab for t in range(r - 1))
    return R

def mm(A, B):
    return (A.astype(np.uint16) @ B.astype(np.uint16)) > 0

def main(r, k, limit=None):
    t0 = time.time()
    perms = list(itertools.permutations(range(r)))
    cperms = perms
    std = tuple(1 << i for i in range(r))
    bases = all_bases(r)
    # prefix-set index per permutation
    pref = [[sum(1 << x for x in p[:c]) for c in range(r + 1)] for p in perms]
    full = 1 << r
    seen = set(); cases = 0; pf_fail = 0; pf2_tot = pf2_bad = 0; examples = []
    it = itertools.product(bases, repeat=k - 1)
    for rest in it:
        if k == 3 and rest[0] > rest[1]:
            continue                      # (B2, B3) and (B3, B2) are covered by the two cyclic orders
        key = canon(rest, r, cperms)
        if key in seen:
            continue
        seen.add(key)
        cases += 1
        vecs = list(std) + [v for B in rest for v in B]
        tab = table(vecs, r)
        Bs = [tuple(range(i * r, (i + 1) * r)) for i in range(k)]
        orders = [tuple(range(k))] if k == 2 else [tuple(range(k)), (0,) + tuple(range(k - 1, 0, -1))]
        bad = False
        for o in orders:
            seq = [Bs[i] for i in o]
            rels = [serial_rel(seq[i], seq[(i + 1) % k], tab, perms, r) for i in range(k)]
            for i in range(k):
                P = rels[i]
                for j in range(1, k):
                    P = mm(P, rels[(i + j) % k])
                ok = P.diagonal()
                got = set()
                for flag, pr in zip(ok, pref):
                    if flag:
                        got.update(pr)
                if len(got) != full:
                    bad = True
            if k == 2:
                G = rels[0] & rels[1].T
                real = set()
                idx = np.argwhere(G)
                for a, b in idx:
                    for c in range(1, r):
                        real.add((pref[a][c], pref[b][c]))
                A, B = seq
                for c in range(1, r):
                    for T in itertools.combinations(range(r), c):
                        mT = sum(1 << x for x in T)
                        restA = sum(1 << A[x] for x in range(r) if x not in T)
                        inA = sum(1 << A[x] for x in T)
                        for T2 in itertools.combinations(range(r), c):
                            mT2 = sum(1 << x for x in T2)
                            restB = sum(1 << B[x] for x in range(r) if x not in T2)
                            inB = sum(1 << B[x] for x in T2)
                            if (restA | inB) in tab and (restB | inA) in tab:
                                pf2_tot += 1
                                if (mT, mT2) not in real:
                                    pf2_bad += 1
        if bad:
            pf_fail += 1
            if len(examples) < 3:
                examples.append(rest)
        if limit and cases >= limit:
            break
    print("rank %d, k=%d over GF(2): %d inequivalent cases, PF fails in %d  (%.0fs)" % (
        r, k, cases, pf_fail, time.time() - t0))
    if k == 2:
        print("   PF2: %d symmetric-exchange pairs, %d not realised as initial segments" % (pf2_tot, pf2_bad))
    for e in examples:
        print("   PF failure:", e)
    sys.stdout.flush()

if __name__ == "__main__":
    for s in sys.argv[1:]:
        a = list(map(int, s.split(",")))
        main(*a)
