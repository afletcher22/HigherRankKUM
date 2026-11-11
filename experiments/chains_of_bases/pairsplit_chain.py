"""The refinement tree 5 = 1 + (2 + 2) on chains of bases of strict binary matroids of rank 5.

For a random partition of the ground set into k bases B_0, ..., B_{k-1} in a cyclic order and
every choice of x_i in B_i with B_i - x_i + x_{i+1} a basis (the root split), let W_i = B_i - x_i.
The 4-blocks W_i form a twisted chain with N_i = M / x_{i+1}.  For each such choice the script
records

  * whether some relation of the pair-split cycle is slack (meets all 24 bijections);
  * whether the pair-split cycle closes (a closed walk of 2-subsets);
  * whether the W-chain closes completely (then x_0 W_0 x_1 W_1 ... is a cyclic basis ordering).

Usage: python pairsplit_chain.py k n_matroids n_partitions seed [k6 | r10]
(k6: the cycle matroid of K_6, rank 5 on 15 elements, k = 3; r10: the regular matroid R10, k = 2)
"""
import itertools, random, sys, time
import numpy as np
from chainlib import Ctx, mm
from schemeR5 import strict_matroid, rank2
from pairsplit_local import PAIRS, IND

R = 5


def all_bases(vecs):
    n = len(vecs)
    return {sum(1 << i for i in c) for c in itertools.combinations(range(n), R)
            if rank2([vecs[i] for i in c]) == R}


def random_partition(n, k, bases, rng):
    """Random partition of range(n) into k bases, or None."""
    blist = list(bases)
    def rec(free, k):
        if k == 0: return []
        low = free & -free
        cand = [b for b in blist if b & low and b & ~free == 0]
        rng.shuffle(cand)
        for b in cand:
            rest = rec(free & ~b, k - 1)
            if rest is not None: return [b] + rest
        return None
    return rec((1 << n) - 1, k)


def elems(mask):
    return [i for i in range(mask.bit_length()) if mask >> i & 1]


def named(name):
    if name == "k6":      # edge ij -> e_i + e_j, last coordinate dropped
        return [((1 << i) ^ (1 << j)) & 31 for i, j in itertools.combinations(range(6), 2)]
    circ = ["11001", "11100", "01110", "00111", "10011"]
    return [1 << i for i in range(5)] + [sum(int(circ[i][j]) << i for i in range(5)) for j in range(5)]


def study_chain(B, bases, ctx):
    """B: list of k bases (lists of element indices), bases: set of bitmasks of all bases.
    Yields (x, slack, split, full) for every choice of x with a valid root split."""
    k = len(B)
    for xs in itertools.product(range(R), repeat=k):
        x = [B[i][xs[i]] for i in range(k)]
        W = [[e for e in B[i] if e != x[i]] for i in range(k)]
        wm = [sum(1 << e for e in w) for w in W]
        if any((wm[i] | 1 << x[(i + 1) % k]) not in bases for i in range(k)): continue
        Ts = []; slack = False
        for i in range(k):
            j = (i + 1) % k
            T = np.zeros((6, 6), dtype=bool)
            for a, Q in enumerate(PAIRS):
                qm = (1 << W[i][Q[0]]) | (1 << W[i][Q[1]]) | (1 << x[j])
                for b, Qp in enumerate(PAIRS):
                    pm = wm[j] & ~((1 << W[j][Qp[0]]) | (1 << W[j][Qp[1]]))
                    T[a, b] = (qm | pm) in bases
            Ts.append(T)
            if all(T[np.arange(6), IND[p]].any() for p in range(24)): slack = True
        P = Ts[0]
        for T in Ts[1:]: P = mm(P, T)
        split = bool(P.diagonal().any())
        rels = [ctx.rel(W[i], W[(i + 1) % k],
                        lambda idx, xx=x[(i + 1) % k]: (sum(1 << e for e in idx) | 1 << xx) in bases)
                for i in range(k)]
        full = bool(ctx.closed(rels).any())
        yield x, slack, split, full


def main(k, n_mat, n_part, seed, name=None):
    rng = random.Random(seed); t0 = time.time(); n = R * k
    ctx = Ctx(4)
    tot = dict(chains=0, valid=0, slack=0, split=0, full=0, tight_split=0, tight_full=0,
               chain_full=0, split_nofull=0)
    for mi in range(n_mat):
        vecs = named(name) if name else strict_matroid(R, k, rng)
        bases = all_bases(vecs)
        loc = dict.fromkeys(tot, 0)
        for _ in range(n_part):
            part = random_partition(n, k, bases, rng)
            if part is None: continue
            rng.shuffle(part)
            loc["chains"] += 1
            any_full = False
            for x, slack, split, full in study_chain([elems(b) for b in part], bases, ctx):
                loc["valid"] += 1
                loc["slack"] += slack; loc["split"] += split; loc["full"] += full
                if not slack:
                    loc["tight_split"] += split; loc["tight_full"] += full
                if split and not full: loc["split_nofull"] += 1
                any_full |= full
            loc["chain_full"] += any_full
        for key in tot: tot[key] += loc[key]
        print("matroid %d: %s  [%.0fs]" % (mi, loc, time.time() - t0), flush=True)
    v = max(tot["valid"], 1)
    print("TOTAL k=%d: chains %d, with a closing choice of x: %d" % (k, tot["chains"], tot["chain_full"]))
    print("choices of x with a valid root split: %d" % tot["valid"])
    print("  some relation slack:      %d (%.1f%%)" % (tot["slack"], 100.0 * tot["slack"] / v))
    print("  pair-split closes:        %d (%.2f%%)" % (tot["split"], 100.0 * tot["split"] / v))
    print("  W-chain closes fully:     %d (%.2f%%)" % (tot["full"], 100.0 * tot["full"] / v))
    print("  split closes, chain does not: %d" % tot["split_nofull"])
    print("  all relations tight: %d, of which split closes %d, chain closes %d" % (
        tot["valid"] - tot["slack"], tot["tight_split"], tot["tight_full"]))


if __name__ == "__main__":
    main(*map(int, sys.argv[1:5]), *sys.argv[5:6])
