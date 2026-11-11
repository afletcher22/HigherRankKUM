"""Adversarial version of pairsplit_chain.py: chains of k bases given by sparse random invertible
5 x 5 matrices over GF(2) (no density assumption; parallel elements and many dependencies).

Usage: python pairsplit_adv.py k n_chains seed
"""
import random, sys, time
from chainlib import Ctx
from schemeR5 import rank2
from pairsplit_chain import R, all_bases, study_chain


def sparse_basis(rng):
    while True:
        d = rng.uniform(0.2, 0.6)
        vs = [sum(1 << i for i in range(R) if rng.random() < d) for _ in range(R)]
        if rank2(vs) == R: return vs


def main(k, n_chains, seed):
    rng = random.Random(seed); t0 = time.time(); ctx = Ctx(4)
    tot = dict(valid=0, slack=0, split=0, full=0, chain_full=0, chains_with_valid=0)
    bad = []
    for c in range(n_chains):
        vecs = [1 << i for i in range(R)]
        for _ in range(k - 1): vecs += sparse_basis(rng)
        bases = all_bases(vecs)
        B = [list(range(R * i, R * i + R)) for i in range(k)]
        anyf = False; anyv = False
        for x, slack, split, full in study_chain(B, bases, ctx):
            anyv = True
            tot["valid"] += 1; tot["slack"] += slack; tot["split"] += split; tot["full"] += full
            anyf |= full
            if not split: bad.append((vecs, x))
        tot["chain_full"] += anyf; tot["chains_with_valid"] += anyv
        if (c + 1) % 500 == 0: print(c + 1, tot, "[%.0fs]" % (time.time() - t0), flush=True)
    print("TOTAL k=%d chains=%d:" % (k, n_chains), tot)
    print("root splits whose pair-split cycle does not close: %d" % len(bad))
    for vecs, x in bad[:5]: print("  example:", [format(v, "05b") for v in vecs], "x =", x)


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
