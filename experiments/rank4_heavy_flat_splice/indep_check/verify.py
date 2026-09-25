"""Independent verification helpers (different axiom system from the CNF):
full rank function on the whole power set via subset-max DP, then brute-force check of
the rank axioms (normalised, r<=|X|, monotone, unit increase, submodular), then a direct
check of the counterexample property using the insertion-based enumerator (method 2).
"""
import pickle
import sys

import numpy as np

import common


def rank_from_ind(n, ind):
    """r(X) = max |Y| over Y subset X with ind[Y] (|Y|<=4)."""
    size = 1 << n
    r = np.zeros(size, dtype=np.int8)
    for m, v in ind.items():
        if v:
            r[m] = common.popcount(m)
    idx = np.arange(size)
    for i in range(n):
        b = 1 << i
        has = (idx & b) != 0
        r[has] = np.maximum(r[has], r[idx[has] ^ b])
    return r


def check_rank_axioms(n, r):
    size = 1 << n
    idx = np.arange(size)
    pc = np.array([bin(m).count("1") for m in range(size)], dtype=np.int8)
    errs = []
    if r[0] != 0:
        errs.append("r(empty)!=0")
    if np.any(r > pc):
        errs.append("r(X)>|X|")
    for i in range(n):
        b = 1 << i
        X = idx[(idx & b) == 0]
        d = r[X | b].astype(int) - r[X]
        if np.any(d < 0) or np.any(d > 1):
            errs.append(f"monotone/unit fails at element {i}")
    for i in range(n):
        for j in range(i + 1, n):
            a, b = 1 << i, 1 << j
            X = idx[(idx & (a | b)) == 0]
            lhs = r[X | a].astype(int) + r[X | b]
            rhs = r[X | a | b].astype(int) + r[X]
            if np.any(lhs < rhs):
                errs.append(f"submodularity fails for pair {i},{j}")
    return errs


def check_counterexample(kind, P, rankfun):
    """rankfun(mask) -> rank.  Returns (hypotheses_ok, n_interleavings, n_bad)."""
    if kind == "A":
        forced = common.linear_forced(P)
        inter = common.linear_interleavings_insert(P)
        wins = common.linear_windows
    else:
        forced = common.cyclic_forced(P)
        inter = common.cyclic_interleavings_insert(P)
        wins = common.cyclic_windows
    hyp = all(rankfun(f) == 4 for f in forced)
    # an interleaving is "good" (proves the claim for this matroid) if all windows are bases
    good = [seq for seq in inter if all(rankfun(w) == 4 for w in wins(seq))]
    return hyp, len(inter), len(good), (good[0] if good else None)


def verify_exact_model(path):
    with open(path, "rb") as f:
        d = pickle.load(f)
    n, kind, P, ind = d["n"], d["kind"], d["P"], d["ind"]
    r = rank_from_ind(n, ind)
    errs = check_rank_axioms(n, r)
    # the ind family must be recovered as {X : r(X)=|X|}
    rec = all((r[m] == common.popcount(m)) == v for m, v in ind.items())
    full = int(r[(1 << n) - 1])
    hyp, ni, ngood, _ = check_counterexample(kind, P, lambda m: int(r[m]))
    nb = sum(1 for m, v in ind.items() if common.popcount(m) == 4 and not v)
    print(f"{path}: n={n} rank(E)={full} axiom_errors={errs or 'none'} "
          f"ind_recovered={rec} hypotheses_hold={hyp} interleavings={ni} "
          f"good_interleavings={ngood} non-bases(4-sets)={nb}")
    loops = [i for i in range(n) if not ind[1 << i]]
    par = [(i, j) for i in range(n) for j in range(i + 1, n) if not ind[(1 << i) | (1 << j)]]
    print(f"   loops={loops} parallel_pairs={len(par)}")
    return not errs and rec and full == 4 and hyp and ngood == 0


if __name__ == "__main__":
    ok = all(verify_exact_model(p) for p in sys.argv[1:])
    print("ALL VERIFIED" if ok else "VERIFICATION FAILED")
