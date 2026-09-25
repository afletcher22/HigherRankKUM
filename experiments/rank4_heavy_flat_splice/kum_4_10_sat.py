"""Direct SAT check of rank-4 KUM on 10 elements (representation-free).

Claim: every uniformly dense (4|S| <= 10 r(S)) rank-4 matroid on 10 elements has a cyclic
basis ordering.  Encoding: rank function on all 1024 subsets (order encoding) with the local
rank axioms, density, and for every cyclic order of {0..9} (0 first, one of each
reflection pair) a clause saying some 4-window is dependent.  UNSAT proves the claim.

Optional argument 'strict' adds points<=2, lines<=4, planes<=6 (strict, t=0 at k=2).
"""
import itertools, sys, time
from pysat.solvers import Cadical153
from base_sat_general import rank_axioms, var

N = 10


def no_big(j, size):
    return [[var(sum(1 << x for x in S), j + 1)] for S in itertools.combinations(range(N), size)]


def build(strict=False):
    cl = rank_axioms()
    if strict:
        cl += no_big(1, 3) + no_big(2, 5) + no_big(3, 7)
    n = 0
    for rest in itertools.permutations(range(1, N)):
        if rest[0] > rest[-1]:
            continue                      # keep one of each reflection pair
        seq = (0,) + rest
        wins = {sum(1 << seq[(i + j) % N] for j in range(4)) for i in range(N)}
        cl.append([-var(W, 4) for W in wins])
        n += 1
    return cl, n


if __name__ == "__main__":
    strict = len(sys.argv) > 1 and sys.argv[1] == "strict"
    t = time.time()
    cl, n = build(strict)
    print(f"clauses={len(cl)} cyclic orders={n} (built {time.time()-t:.0f}s)", flush=True)
    s = Cadical153(bootstrap_with=cl)
    res = s.solve()
    print(("SAT: a uniformly dense rank-4 10-element matroid WITHOUT a CBO exists"
           if res else "UNSAT: every uniformly dense rank-4 matroid on 10 elements has a CBO"),
          f"({time.time()-t:.0f}s)", flush=True)
    if res:
        m = set(l for l in s.get_model() if l > 0)
        r = lambda S: sum(1 for v in range(1, 5) if var(S, v) in m)
        print("non-bases:", [B for B in itertools.combinations(range(N), 4)
                             if r(sum(1 << x for x in B)) < 4])
