"""Does every chain of three bases have a root split whose 4-blocks close completely?  Structured
chains over F_2 built as in pairsplit_tightsearch.py (two rigid relations, or two tight ones),
without any density assumption.  Reports the chains with no closing root split by margin
(> 0 strict, 0 tight flat, < 0 not uniformly dense).

Usage: python pairsplit_structured.py rigid|tight n_chains seed
"""
import random, sys, time
from collections import Counter
from chainlib import Ctx
from pairsplit_chain import all_bases, study_chain
import pairsplit_tightsearch as ts


def main(mode, n, seed):
    rng = random.Random(seed); t0 = time.time(); ctx = Ctx(4)
    I4 = [[int(i == j) for j in range(4)] for i in range(4)]
    tm = [I4] if mode == "rigid" else ts.tight_matrices()
    done = 0; by_margin = Counter(); none = Counter(); nosplit = Counter(); example = None
    while done < n:
        S0, S1 = rng.choice(tm), rng.choice(tm)
        u = [rng.randrange(2) for _ in range(4)]; up = [rng.randrange(2) for _ in range(4)]
        x, W = ts.build(S0, u, rng.randrange(1, 32) | 1, S1, up, rng.randrange(1, 32))
        if ts.study(x, W) is None: continue
        vecs = [x[0]] + W[0] + [x[1]] + W[1] + [x[2]] + W[2]
        m = ts.margin(vecs)
        r = list(study_chain([list(range(0, 5)), list(range(5, 10)), list(range(10, 15))], all_bases(vecs), ctx))
        done += 1; by_margin[m] += 1
        if not any(a[2] for a in r): nosplit[m] += 1
        if not any(a[3] for a in r):
            none[m] += 1
            if example is None or m > example[0]: example = (m, vecs)
        if done % 1000 == 0:
            print(done, "chains by margin", dict(sorted(by_margin.items())), "| no pair split for any root split",
                  dict(sorted(nosplit.items())), "| no closing root split", dict(sorted(none.items())),
                  "[%.0fs]" % (time.time() - t0), flush=True)
    print("TOTAL %s: chains by margin %s" % (mode, dict(sorted(by_margin.items()))))
    print("  no pair split for any root split:", dict(sorted(nosplit.items())))
    print("  no closing root split:", dict(sorted(none.items())))
    if example: print("  example (margin %d): %s" % (example[0], [format(v, "05b") for v in example[1]]))


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))
