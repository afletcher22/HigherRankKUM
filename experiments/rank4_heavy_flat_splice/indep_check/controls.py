"""Controls:
 1. Known genuine Claim-B counterexample at N=6 (binary): verified directly by brute force,
    then plugged into the FULL CNFs (E1 and E2) of B6 -> every clause must be satisfied.
 2. Positive axiom controls: random GF(2)/GF(3)/GF(5) rank-4 matroids on 18 elements satisfy
    all axiom clauses of E1 and of E2 (A14 blocks).  U_{4,18} additionally satisfies the
    hypotheses but must violate EVERY interleaving clause (all windows are bases).
 3. Negative axiom controls: three non-matroids must be rejected by E1 and by E2.
"""
import random
from itertools import combinations

import common
from cnf_enc import block_cnf, exact_cnf, submasks
from pysat.solvers import Solver


def gf_rank(vecs, p):
    rows = [list(v) for v in vecs]
    rk, col, m = 0, 0, len(rows[0]) if rows else 0
    while rk < len(rows) and col < m:
        piv = next((i for i in range(rk, len(rows)) if rows[i][col] % p), None)
        if piv is None:
            col += 1
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][col], p - 2, p)
        rows[rk] = [(x * inv) % p for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][col] % p:
                f = rows[i][col]
                rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[rk])]
        rk += 1
        col += 1
    return rk


def int_to_vec2(x):
    return [(x >> i) & 1 for i in range(4)]


def rank_fun_from_vectors(vecs, p):
    cache = {}

    def r(m):
        if m not in cache:
            cache[m] = gf_rank([vecs[i] for i in range(len(vecs)) if m >> i & 1], p)
        return cache[m]
    return r


def assign_exact(var, rf):
    return {v: rf(m) == common.popcount(m) for m, v in var.items()}


def assign_block(var, rf):
    return {v: rf(X) >= k for (X, k), v in var.items()}


def falsified(cls, asg):
    return [c for c in cls if not any(asg[abs(l)] == (l > 0) for l in c)]


def run_full_on(kind, P, rf, label):
    n, forced, blocks, inter, cs = common.instance(kind, P)
    var1, cls1, _ = exact_cnf(n, forced, cs)
    var2, cls2, _ = block_cnf(n, blocks, forced, cs)
    f1 = falsified(cls1, assign_exact(var1, rf))
    f2 = falsified(cls2, assign_block(var2, rf))
    print(f"  {label}: falsified clauses E1={len(f1)}  E2={len(f2)}")
    return f1, f2, len(cs)


def axioms_only(n, blocks, rf):
    var1, cls1, _ = exact_cnf(n, [], [])
    var2, cls2, _ = block_cnf(n, blocks, [], [])
    return (len(falsified(cls1, assign_exact(var1, rf))),
            len(falsified(cls2, assign_block(var2, rf))))


def main():
    from verify import check_counterexample
    ok = True
    # ------------------------------------------------------------------ 1
    print("Control 1: binary N=6 counterexample, S={1,2,4,8}, cycle (1,6,8,3,4,10)")
    vecs = [int_to_vec2(x) for x in (1, 2, 4, 8, 1, 6, 8, 3, 4, 10)]
    rf = rank_fun_from_vectors(vecs, 2)
    hyp, ni, ngood, g = check_counterexample("B", 6, rf)
    print(f"  direct brute force: hypotheses hold={hyp}, interleavings={ni}, "
          f"interleavings with all windows bases={ngood}")
    ok &= hyp and ngood == 0
    f1, f2, _ = run_full_on("B", 6, rf, "binary example in full B6 CNFs")
    ok &= not f1 and not f2
    # also confirm by the solver with the matroid fixed through assumptions
    n, forced, blocks, inter, cs = common.instance("B", 6)
    var1, cls1, _ = exact_cnf(n, forced, cs)
    asm = [v if b else -v for v, b in assign_exact(var1, rf).items()]
    with Solver(name="cadical195", bootstrap_with=cls1) as s:
        r = s.solve(assumptions=asm)
    print(f"  E1(B6) solve under assumptions = binary matroid: {'SAT' if r else 'UNSAT'}")
    ok &= r
    # same binary matroid in B7 is NOT applicable (different N) -- instead check that a
    # binary matroid's truncation trick is irrelevant; skip.

    # ------------------------------------------------------------------ 2
    print("Control 2: random representable rank-4 matroids on 18 elements (A14 blocks)")
    rng = random.Random(12345)
    n = 18
    blocks = common.linear_blocks(14)
    for p in (2, 3, 5):
        for trial in range(3):
            while True:
                vecs = [[rng.randrange(p) for _ in range(4)] for _ in range(n)]
                if gf_rank(vecs, p) == 4:
                    break
            rf = rank_fun_from_vectors(vecs, p)
            a1, a2 = axioms_only(n, blocks, rf)
            nb = sum(1 for c in combinations(range(n), 4) if rf(common.mask(c)) < 4)
            print(f"  GF({p}) trial {trial}: non-bases={nb}, falsified axiom clauses E1={a1} E2={a2}")
            ok &= a1 == 0 and a2 == 0
    uni = lambda m: min(common.popcount(m), 4)
    f1, f2, ncs = run_full_on("A", 14, uni, "U_{4,18} in full A14 CNFs")
    ok &= len(f1) == ncs and len(f2) == ncs
    print(f"  (expected: exactly the {ncs} interleaving clauses falsified, nothing else)")

    # ------------------------------------------------------------------ 3
    print("Control 3: non-matroids must be rejected (axiom clauses only, A14 blocks)")
    s0, s1 = 1, 2
    t = [0b1111, 1 << 4, 1 << 5]

    def rf_ab(m):  # all <=4-sets independent except 4-sets containing s0 and s1
        best = 0
        for k in range(min(4, common.popcount(m)), -1, -1):
            for c in combinations([i for i in range(n) if m >> i & 1], k):
                cm = common.mask(c)
                if not (k == 4 and cm & (s0 | s1) == (s0 | s1)):
                    return k
        return best

    T3 = 0b0111  # s0,s1,s2
    def rf_hered(m):  # uniform, but one 3-set declared rank 2 (supersets untouched)
        return 2 if m == T3 else min(common.popcount(m), 4)

    T = 0b0111
    a, b = 1 << 3, 1 << 4          # s3 and e_0
    W1, W2 = T | a, T | b

    def rf_sub(m):  # uniform except W1, W2 and T+a+b-supersets handled naively
        # max over subsets of size<=4 excluding the two declared non-bases
        pc = common.popcount(m)
        if pc <= 3:
            return pc
        if pc == 4:
            return 3 if m in (W1, W2) else 4
        return 4

    for name, rf in (("augmentation-violating family (s0,s1 in no basis)", rf_ab),
                     ("hereditary-violating (one 3-set dependent)", rf_hered),
                     ("two 4-sets T+a, T+b dependent but {t1,t2,a,b} independent", rf_sub)):
        a1, a2 = axioms_only(n, blocks, rf)
        print(f"  {name}: falsified axiom clauses E1={a1} E2={a2}")
        ok &= a1 > 0 and a2 > 0
    print("ALL CONTROLS PASSED" if ok else "SOME CONTROL FAILED")


if __name__ == "__main__":
    main()
