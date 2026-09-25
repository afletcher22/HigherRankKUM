"""Direct SAT check of rank-4 KUM on N elements (representation-free), N <= 10.

Claim: every uniformly dense (4|X| <= N r(X)) rank-4 matroid on N elements has a CBO.
Rank function on all 2^N subsets (order encoding) with the local rank axioms and density, plus
one clause per cyclic order (0 first, one of each reflection pair) saying a window is dependent.
UNSAT proves the claim.  Control: dropping density must give SAT (e.g. a matroid with a
parallel class of size > N/4 has no CBO).

Usage: python kum_small_sat.py N [nodensity]
"""
import itertools, sys, time
from pysat.solvers import Cadical153


def run(N, density=True):
    var = lambda X, v: X * 4 + v
    pc = lambda X: bin(X).count("1")
    cl = []
    for X in range(1 << N):
        for v in range(1, 4):
            cl.append([-var(X, v + 1), var(X, v)])
        for v in range(pc(X) + 1, 5):
            cl.append([-var(X, v)])
        need = -(-4 * pc(X) // N)
        if density and need >= 1:
            cl.append([var(X, min(need, 4))] if need <= 4 else [])
    cl.append([var((1 << N) - 1, 4)])
    for X in range(1 << N):
        for a in range(N):
            if X >> a & 1:
                continue
            T = X | 1 << a
            for v in range(1, 5):
                cl.append([-var(X, v), var(T, v)])
                if v < 4:
                    cl.append([-var(T, v + 1), var(X, v)])
            for b in range(a + 1, N):
                if X >> b & 1:
                    continue
                U, Xb = T | 1 << b, X | 1 << b
                for v in range(1, 5):
                    c = [-var(U, v), var(T, v), var(Xb, v), var(X, v)]
                    if v >= 2:
                        c.append(-var(X, v - 1))
                    cl.append(c)
    n = 0
    for rest in itertools.permutations(range(1, N)):
        if rest[0] > rest[-1]:
            continue
        seq = (0,) + rest
        cl.append([-var(sum(1 << seq[(i + j) % N] for j in range(4)), 4) for i in range(N)])
        n += 1
    cl = [c for c in cl if c]
    t = time.time()
    s = Cadical153(bootstrap_with=cl)
    res = s.solve()
    print(f"N={N} density={density}: {n} cyclic orders -> "
          f"{'SAT (matroid without CBO)' if res else 'UNSAT: every uniformly dense rank-4 matroid on N elements has a CBO'} "
          f"({time.time()-t:.0f}s)", flush=True)
    return res


if __name__ == "__main__":
    N = int(sys.argv[1])
    run(N, density="nodensity" not in sys.argv)
