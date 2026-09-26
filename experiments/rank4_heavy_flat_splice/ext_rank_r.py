"""The extension theorem X' in rank r, as a SAT experiment.

X'(r, N): let S be a basis of a rank-r matroid, and e_0, ..., e_{N-1} a cyclic ordering of the
other N elements whose r-windows are all bases. Then S can be interleaved into the cyclic
sequence so that every r-window of the merged sequence is a basis.

Encoding, as in ext_witness.py for r = 4: positions 0..r-1 are S, position r+i is e_i. Variable
(r+1)X + v means r(X) >= v (1 <= v <= r). Rank axioms are imposed on the subsets of every block
S + {w cyclically consecutive e's}. Unit clauses make S and every r-window of the e's a basis. One
clause per interleaving (an order of S and a multiset of insertion gaps) says that some window of
the merged sequence containing an element of S is not a basis. UNSAT proves X'(r, N).

Usage: python ext_rank_r.py r N [w] [dense] [paving] [indepJ]   (w defaults to r + 2; indepJ makes
every set of at most J elements independent; dense adds the
density of M and of M - S as lower bounds on ranks; paving makes every set of at most r - 1
elements independent, the setting of McGuinness, Cyclic orderings of paving matroids, Prop. 5.2)
"""
import itertools, sys, time
from pysat.solvers import Cadical195


def build(r, N, w, dense=False, paving=False, indep=0):
    B = r + 1
    var = lambda X, v: B * X + v
    mask = lambda ps: sum(1 << p for p in ps)
    pc = lambda X: bin(X).count("1")
    cls, seen = [], set()

    def add(c):
        t = tuple(c)
        if t not in seen:
            seen.add(t)
            cls.append(list(c))

    E = [r + i for i in range(N)]
    S = list(range(r))
    done = set()
    for i in range(N):
        blk = sorted(S + [E[(i + j) % N] for j in range(w)])
        subsets = [mask(c) for k in range(len(blk) + 1) for c in itertools.combinations(blk, k)]
        for X in subsets:
            if X in done:
                continue
            done.add(X)
            for v in range(1, r):
                add([-var(X, v + 1), var(X, v)])
            for v in range(pc(X) + 1, r + 1):
                add([-var(X, v)])
        for X in subsets:
            out = [x for x in blk if not X >> x & 1]
            for a in out:
                T = X | 1 << a
                for v in range(1, r + 1):
                    add([-var(X, v), var(T, v)])
                    if v < r:
                        add([-var(T, v + 1), var(X, v)])
                for b in out:
                    if b <= a:
                        continue
                    U, Xb = T | 1 << b, X | 1 << b
                    for v in range(1, r + 1):
                        c = [-var(U, v), var(T, v), var(Xb, v), var(X, v)]
                        if v >= 2:
                            c.append(-var(X, v - 1))
                        add(c)
    if dense:
        # M uniformly dense on N + r elements, and M - S uniformly dense on N elements
        for X in done:
            need = -(-r * pc(X) // (N + r))
            if X & mask(S) == 0:
                need = max(need, -(-r * pc(X) // N))
            if need >= 1:
                add([var(X, min(need, r))])
    if paving:
        indep = max(indep, r - 1)
    # every set of at most `indep` elements is independent (paving: indep = r - 1)
    for X in done:
        if 1 <= pc(X) <= indep:
            add([var(X, pc(X))])
    add([var(mask(S), r)])
    for i in range(N):
        add([var(mask(E[(i + t) % N] for t in range(r)), r)])
    n = 0
    for perm in itertools.permutations(S):
        for gs in itertools.combinations_with_replacement(range(N), r):
            seq, gi = [], 0
            for pos in range(N):
                while gi < r and gs[gi] == pos:
                    seq.append(perm[gi]); gi += 1
                seq.append(E[pos])
            L = len(seq)
            lits = []
            for j in range(L):
                W = [seq[(j + t) % L] for t in range(r)]
                if any(x < r for x in W):
                    lits.append(-var(mask(W), r))
            add(lits)
            n += 1
    return cls, n


if __name__ == "__main__":
    r, N = int(sys.argv[1]), int(sys.argv[2])
    w = int(sys.argv[3]) if len(sys.argv) > 3 else r + 2
    dense = "dense" in sys.argv[4:]
    paving = "paving" in sys.argv[4:]
    indep = max([int(a[5:]) for a in sys.argv[4:] if a.startswith("indep")], default=0)
    t = time.time()
    cls, n = build(r, N, w, dense, paving, indep)
    print(f"r={r} N={N} w={w}: {len(cls)} clauses, {n} interleavings (built {time.time() - t:.0f}s)",
          flush=True)
    s = Cadical195(bootstrap_with=cls)
    res = s.solve()
    print(f"  -> {'SAT: X fails (or the local encoding is too weak)' if res else 'UNSAT: X holds'}"
          f" ({time.time() - t:.0f}s)", flush=True)
