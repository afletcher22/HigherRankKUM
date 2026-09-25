"""Usage: python run.py {A|B} P {exact|block} [solver]

Builds the instance, cross-checks the interleaving enumeration against an independent
generator, solves, and (if SAT) saves the model to models/<kind><P>_<enc>.pkl.
"""
import os
import pickle
import sys
import time

from pysat.solvers import Solver

import common
from cnf_enc import block_cnf, exact_cnf


def main():
    kind, P, enc = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    sname = sys.argv[4] if len(sys.argv) > 4 else "cadical195"
    t0 = time.time()
    n, forced, blocks, inter, cs = common.instance(kind, P)
    # independent enumeration cross-check
    if kind == "A":
        alt = common.linear_interleavings_insert(P)
        formula = (P - 5) * (P - 4) * (P - 3) * (P - 2)
    else:
        alt = common.cyclic_interleavings_insert(P)
        formula = P * (P + 1) * (P + 2) * (P + 3)
    s1, s2 = set(inter), set(alt)
    assert len(inter) == len(s1), "method 1 produced duplicates"
    assert len(alt) == len(s2), "method 2 produced duplicates"
    assert s1 == s2, "enumerations disagree"
    assert len(s1) == formula
    print(f"[{kind}{P} {enc}] n={n} interleavings={len(inter)} (formula {formula}, "
          f"two generators agree) distinct clauses={len(cs)}", flush=True)
    if enc == "exact":
        var, cls, nv = exact_cnf(n, forced, cs)
    else:
        var, cls, nv = block_cnf(n, blocks, forced, cs)
    t1 = time.time()
    print(f"[{kind}{P} {enc}] vars={nv} clauses={len(cls)} build={t1 - t0:.1f}s", flush=True)
    with Solver(name=sname, bootstrap_with=cls) as s:
        t2 = time.time()
        res = s.solve()
        t3 = time.time()
        print(f"[{kind}{P} {enc}] solver={sname} result={'SAT' if res else 'UNSAT'} "
              f"solve={t3 - t2:.2f}s (load {t2 - t1:.1f}s)", flush=True)
        if res:
            model = set(l for l in s.get_model() if l > 0)
            os.makedirs("models", exist_ok=True)
            if enc == "exact":
                ind = {m: (v in model) for m, v in var.items()}
                data = {"kind": kind, "P": P, "n": n, "ind": ind}
            else:
                rank = {}
                for (X, k), v in var.items():
                    if v in model:
                        rank[X] = max(rank.get(X, 0), k)
                    else:
                        rank.setdefault(X, 0)
                data = {"kind": kind, "P": P, "n": n, "rank": rank}
            with open(f"models/{kind}{P}_{enc}.pkl", "wb") as f:
                pickle.dump(data, f)


if __name__ == "__main__":
    main()
