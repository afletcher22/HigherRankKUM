"""KUM(r, n) as a SAT claim: every uniformly dense rank-r matroid on n elements
(r |X| <= n r(X) for all X) has a cyclic basis ordering.

Rank function on all 2^n subsets (variable (r+1)X + v means r(X) >= v), the local rank axioms,
density, and one clause per cyclic order (0 first, one of each reflection pair) saying that some
r-window is not a basis. UNSAT proves KUM(r, n). Writes certs/kumR_N.cnf for lrat_native.py.

Usage: python kum_r_n.py r n
"""
import itertools, os, sys, time
from pysat.solvers import Cadical195
from cert_measure import OUT


def build(r, n):
    B = r + 1
    var = lambda X, v: B * X + v
    pc = lambda X: bin(X).count("1")
    cls = []
    for X in range(1 << n):
        for v in range(1, r):
            cls.append([-var(X, v + 1), var(X, v)])
        for v in range(pc(X) + 1, r + 1):
            cls.append([-var(X, v)])
        need = -(-r * pc(X) // n)
        if need >= 1:
            cls.append([var(X, min(need, r))])
    for X in range(1 << n):
        for a in range(n):
            if X >> a & 1:
                continue
            T = X | 1 << a
            for v in range(1, r + 1):
                cls.append([-var(X, v), var(T, v)])
                if v < r:
                    cls.append([-var(T, v + 1), var(X, v)])
            for b in range(a + 1, n):
                if X >> b & 1:
                    continue
                U, Xb = T | 1 << b, X | 1 << b
                for v in range(1, r + 1):
                    c = [-var(U, v), var(T, v), var(Xb, v), var(X, v)]
                    if v >= 2:
                        c.append(-var(X, v - 1))
                    cls.append(c)
    norders = 0
    for rest in itertools.permutations(range(1, n)):
        if rest[0] > rest[-1]:
            continue
        seq = (0,) + rest
        cls.append([-var(sum(1 << seq[(i + j) % n] for j in range(r)), r) for i in range(n)])
        norders += 1
    return cls, norders


if __name__ == "__main__":
    r, n = int(sys.argv[1]), int(sys.argv[2])
    t = time.time()
    cls, norders = build(r, n)
    name = f"kum{r}_{n}"
    with open(os.path.join(OUT, f"{name}.cnf"), "w", newline="\n") as f:
        f.write(f"p cnf {max(abs(l) for c in cls for l in c)} {len(cls)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    print(f"{name}: {len(cls)} clauses, {norders} orders (built {time.time() - t:.0f}s)", flush=True)
    s = Cadical195(bootstrap_with=cls)
    res = s.solve()
    print(f"  -> {'SAT: a counterexample exists' if res else 'UNSAT: KUM holds'} ({time.time() - t:.0f}s)",
          flush=True)
