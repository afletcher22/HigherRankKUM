"""Cyclic extension lemma by SAT, for all matroids.

Claim_cyc(N): if M has rank 4, S is a basis and sigma = (e_0..e_{N-1}) is a CBO of M-S, then S
interleaves into sigma to give a CBO of M.

Two encodings:
  * mode "block": rank axioms only inside the cyclic blocks S + {e_i..e_{i+w-1}} (a relaxation;
    UNSAT proves the claim for every matroid);
  * mode "full": the full rank function on all 2^(N+4) subsets, with optional density caps on M
    and on M-S (caps = max sizes of points, lines, planes).

Usage: python cyclic_sat.py N [block|full] [w]
"""
import itertools, sys, time
from pysat.solvers import Cadical153


def axioms_on(B, var, cls, done):
    B = sorted(B)
    pc = lambda X: bin(X).count("1")
    subsets = [sum(1 << x for x in c) for r in range(len(B) + 1) for c in itertools.combinations(B, r)]
    for X in subsets:
        if X in done:
            continue
        done.add(X)
        for v in range(1, 4):
            cls.add((-var(X, v + 1), var(X, v)))
        for v in range(pc(X) + 1, 5):
            cls.add((-var(X, v),))
    for X in subsets:
        out = [x for x in B if not X >> x & 1]
        for a in out:
            T = X | 1 << a
            for v in range(1, 5):
                cls.add((-var(X, v), var(T, v)))
                if v < 4:
                    cls.add((-var(T, v + 1), var(X, v)))
            for b in out:
                if b <= a:
                    continue
                U, Xb = T | 1 << b, X | 1 << b
                for v in range(1, 5):
                    c = [-var(U, v), var(T, v), var(Xb, v), var(X, v)]
                    if v >= 2:
                        c.append(-var(X, v - 1))
                    cls.add(tuple(c))


def build(N, mode="block", w=6, capsM=None, capsY=None):
    ids = {}

    def var(X, v):
        key = (X, v)
        if key not in ids:
            ids[key] = len(ids) + 1
        return ids[key]

    E = [4 + i for i in range(N)]
    cls, done = set(), set()
    if mode == "block":
        for i in range(N):
            axioms_on([0, 1, 2, 3] + [E[(i + j) % N] for j in range(w)], var, cls, done)
    else:
        axioms_on(list(range(N + 4)), var, cls, done)
        allE = list(range(N + 4))
        for caps, ground in ((capsM, allE), (capsY, E)):
            if not caps:
                continue
            for j, cap in enumerate(caps, start=1):
                for c in itertools.combinations(ground, cap + 1):
                    cls.add((var(sum(1 << x for x in c), j + 1),))
    cls.add((var(0b1111, 4),))
    for i in range(N):
        cls.add((var(sum(1 << E[(i + j) % N] for j in range(4)), 4),))
    nint = 0
    for perm in itertools.permutations(range(4)):
        for gs in itertools.combinations_with_replacement(range(N), 4):
            # gap g = immediately before e_g (gap 0 = between e_{N-1} and e_0)
            seq = []
            gi = 0
            for pos in range(N):
                while gi < 4 and gs[gi] == pos:
                    seq.append(perm[gi]); gi += 1
                seq.append(E[pos])
            n = len(seq)
            wins = set()
            for j in range(n):
                W = [seq[(j + t) % n] for t in range(4)]
                if any(x < 4 for x in W):
                    wins.add(sum(1 << x for x in W))
            cls.add(tuple(sorted(-var(W, 4) for W in wins)))
            nint += 1
    return [list(c) for c in cls], ids, nint


def solve(N, mode="block", w=6, capsM=None, capsY=None):
    t = time.time()
    cls, ids, nint = build(N, mode, w, capsM, capsY)
    print(f"N={N} {mode} w={w} capsM={capsM} capsY={capsY}: {len(ids)} vars, {len(cls)} clauses, "
          f"{nint} interleavings (built {time.time()-t:.0f}s)", flush=True)
    s = Cadical153(bootstrap_with=cls)
    res = s.solve()
    print(f"   -> {'SAT (counter-model)' if res else 'UNSAT: claim holds'} ({time.time()-t:.0f}s)", flush=True)
    return res, (set(l for l in s.get_model() if l > 0) if res else None), ids


if __name__ == "__main__":
    N = int(sys.argv[1])
    mode = sys.argv[2] if len(sys.argv) > 2 else "block"
    w = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    solve(N, mode, w)
