"""Prefix freedom: in a chain of k bases, can any subset T of a basis be an initial segment
of that basis in some interval cyclic basis ordering?  (k = 2 is a strengthening of Gabow.)"""
import itertools, random, sys
sys.path.insert(0, '.')
import numpy as np
import cyclic_chain as C

def mm(A, B):
    return (A.astype(np.uint16) @ B.astype(np.uint16)) > 0

def prefix_sets(mask_perm, perms, r):
    """mask_perm: bool per permutation.  Returns set of (frozenset prefix) over allowed perms."""
    out = set()
    for ok, p in zip(mask_perm, perms):
        if ok:
            for c in range(r + 1):
                out.add(frozenset(p[:c]))
    return out

def study(vecs, p, r, k):
    perms = list(itertools.permutations(range(r)))
    tab = C.base_table(vecs, p, r)
    Bs = [tuple(range(i * r, (i + 1) * r)) for i in range(k)]
    res = []
    orders = [tuple(range(k))] if k == 2 else [tuple(range(k)), (0,) + tuple(range(k - 1, 0, -1))]
    for o in orders:
        seq = [Bs[i] for i in o]
        rels = [C.serial_rel(seq[i], seq[(i + 1) % k], tab, perms) for i in range(k)]
        for i in range(k):          # orders of seq[i] lying on a closed walk
            P = rels[i]
            for j in range(1, k):
                P = mm(P, rels[(i + j) % k])
            ok = P.diagonal()
            res.append(len(prefix_sets(ok, perms, r)))
    return res            # each entry: number of realised prefix sets, max 2^r

def run(name, insts, p, r, k):
    full = 2 ** r
    counts = []
    for vecs in insts:
        counts += study(vecs, p, r, k)
    print("%s: (basis, cyclic order) cases %d; all %d prefix sets realised in %d; minimum realised %d" % (
        name, len(counts), full, sum(c == full for c in counts), min(counts)), flush=True)

rng = random.Random(21)
circ = ['11001', '11100', '01110', '00111', '10011']
cols = [tuple(1 if i == j else 0 for i in range(5)) for j in range(5)]
cols += [tuple(int(circ[i][j]) for i in range(5)) for j in range(5)]
run("R10 pair, k=2", [cols], 2, 5, 2)
run("random GF(2) rank 5, k=2", [[v for B in C.random_bases(5, 2, 2, rng) for v in B] for _ in range(60)], 2, 5, 2)
run("random GF(2) rank 4, k=2", [[v for B in C.random_bases(4, 2, 2, rng) for v in B] for _ in range(300)], 2, 4, 2)
run("random GF(2) rank 4, k=3", [[v for B in C.random_bases(4, 3, 2, rng) for v in B] for _ in range(200)], 2, 4, 3)
run("random GF(3) rank 4, k=3", [[v for B in C.random_bases(4, 3, 3, rng) for v in B] for _ in range(100)], 3, 4, 3)
run("R10 pair + third basis, k=3", [cols + C.random_bases(5, 1, 2, rng)[0] for _ in range(12)], 2, 5, 3)
run("random GF(2) rank 5, k=3", [[v for B in C.random_bases(5, 3, 2, rng) for v in B] for _ in range(15)], 2, 5, 3)
