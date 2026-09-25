"""SAT proof of the 10-element base lemma (representation-free).

Claim: every rank-4 matroid M0 on E = K ∪ C (|K|=6, |C|=4) that is uniformly dense
(4|S| <= 10 r(S)) and in which K is a flat of rank 3 has a cyclic basis ordering with a
K-site, i.e. one of the skeletons
    S1 = KKKCKCKCKC,  S2 = KKKCKCCKKC,  S3 = KKKCKKCCKC   (cyclically).
We encode rank functions by the order encoding x[S][v] <=> r(S) >= v (v=1..4) with
  * r(∅)=0, r(S) <= |S|, r(E)=4;
  * monotone and unit increase: r(S) <= r(S+x) <= r(S)+1;
  * local submodularity: r(S)=v-1 and r(S+x+y) >= v  =>  r(S+x) >= v or r(S+y) >= v.
These are the standard rank axioms (R1)-(R3) in local form.  We add density, flatness of K,
optionally a constraint on r(C), and one clause per candidate site-CBO saying that some
window of it is dependent.  UNSAT proves the claim for all matroids.

Usage: python base_sat.py [rC]     (rC in {2,3,4}; omitted = all)
"""
import itertools, sys, time
from pysat.solvers import Cadical153

N = 10
K = list(range(6))
C = list(range(6, 10))
FULL = (1 << N) - 1
SHAPES = ["KKKCKCKCKC", "KKKCKCCKKC", "KKKCKKCCKC"]


def var(S, v):
    return S * 4 + v  # v in 1..4, ids >= 1


def build(rC=None):
    cl = []
    pc = lambda S: bin(S).count("1")
    for S in range(1 << N):
        for v in range(1, 4):
            cl.append([-var(S, v + 1), var(S, v)])          # order encoding
        for v in range(pc(S) + 1, 5):
            cl.append([-var(S, v)])                          # r(S) <= |S|
    cl.append([var(FULL, 4)])
    for S in range(1 << N):
        for x in range(N):
            if S >> x & 1:
                continue
            T = S | 1 << x
            for v in range(1, 5):
                cl.append([-var(S, v), var(T, v)])           # monotone
                if v < 4:
                    cl.append([-var(T, v + 1), var(S, v)])   # unit increase
            for y in range(x + 1, N):
                if S >> y & 1:
                    continue
                U = T | 1 << y
                Sy = S | 1 << y
                for v in range(1, 5):
                    # r(S)=v-1 & r(U)>=v -> r(S+x)>=v or r(S+y)>=v
                    c = [-var(U, v), var(T, v), var(Sy, v), var(S, v)]
                    if v >= 2:
                        c.append(-var(S, v - 1))
                    cl.append(c)
        # uniform density: r(S) >= ceil(4|S|/10)
        need = -(-4 * pc(S) // 10)
        if need >= 1:
            cl.append([var(S, need)])
    Kmask = sum(1 << x for x in K)
    cl.append([var(Kmask, 3)])
    cl.append([-var(Kmask, 4)])
    for c in C:
        cl.append([var(Kmask | 1 << c, 4)])                  # K is a flat
    Cmask = sum(1 << x for x in C)
    if rC is not None:
        cl.append([var(Cmask, rC)])
        if rC < 4:
            cl.append([-var(Cmask, rC + 1)])
    # forbid every site-CBO
    nsite = 0
    for sh in SHAPES:
        for ko in itertools.permutations(K):
            if ko[0] != 0 and sh == SHAPES[0] and False:
                pass
            for co in itertools.permutations(C):
                seq, ki, ci = [], 0, 0
                for s in sh:
                    if s == "K":
                        seq.append(ko[ki]); ki += 1
                    else:
                        seq.append(co[ci]); ci += 1
                wins = set()
                for i in range(N):
                    W = sum(1 << seq[(i + j) % N] for j in range(4))
                    wins.add(W)
                cl.append([-var(W, 4) for W in wins])
                nsite += 1
    return cl, nsite


if __name__ == "__main__":
    cases = [int(sys.argv[1])] if len(sys.argv) > 1 else [2, 3, 4]
    for rC in cases:
        t = time.time()
        cl, nsite = build(rC)
        s = Cadical153(bootstrap_with=cl)
        res = s.solve()
        print(f"r(C)={rC}: clauses={len(cl)} site-candidates={nsite} -> "
              f"{'SAT (counterexample!)' if res else 'UNSAT (base lemma holds)'} ({time.time()-t:.0f}s)",
              flush=True)
        if res:
            model = set(l for l in s.get_model() if l > 0)
            def r(S):
                return sum(1 for v in range(1, 5) if var(S, v) in model)
            bases = [B for B in itertools.combinations(range(N), 4) if r(sum(1 << x for x in B)) == 4]
            print("bases:", bases)
