"""Which interleaving shapes does the extension theorem X' need (rank 4, exact encoding)?

A shape is the multiset of gaps that the four elements of S occupy, up to rotation: a tuple of
gap offsets (0 = g1 <= g2 <= g3 <= g4 < N). Contiguous insertion is the shape (0,0,0,0). For each
shape the clauses forbid every rotation of it and every order of S.

Usage:
  python xshapes.py N list                 all shapes up to rotation and reflection
  python xshapes.py N test SHAPE [SHAPE..] [dense|strict]   is X' UNSAT with only these shapes
                                           (plus always the contiguous shape)?  SHAPE like 0,0,2,5
  python xshapes.py N greedy [dense|strict]  a small set of shapes that suffices, greedily
  add "stream" to feed clauses straight into the solver (N = 12: about 11.5M clauses)
"""
import itertools, sys, time
from pysat.solvers import Cadical195

N = int(sys.argv[1])
mode = sys.argv[2]
opts = [a for a in sys.argv[3:] if a in ("dense", "strict")]
n, r = N + 4, 4
var = lambda X, v: 5 * X + v
pc = lambda X: bin(X).count("1")
mask = lambda c: sum(1 << x for x in c)
S = [0, 1, 2, 3]
E = [4 + i for i in range(N)]


def base(sink=None):
    cls = [] if sink is None else None
    add = cls.append if sink is None else sink
    for X in range(1 << n):
        for v in range(1, r):
            add([-var(X, v + 1), var(X, v)])
        for v in range(pc(X) + 1, r + 1):
            add([-var(X, v)])
        need = 1 if pc(X) >= 1 else 0
        if opts:
            need = max(need, -(-4 * pc(X) // n))
            if X & 15 == 0:
                need = max(need, -(-4 * pc(X) // N))
        if "strict" in opts and 0 < pc(X) < n:
            need = max(need, 4 * pc(X) // n + 1)
        if need:
            add([var(X, min(need, 4))])
    for X in range(1 << n):
        for a in range(n):
            if X >> a & 1:
                continue
            T = X | 1 << a
            for v in range(1, r + 1):
                add([-var(X, v), var(T, v)])
                if v < r:
                    add([-var(T, v + 1), var(X, v)])
            for b in range(a + 1, n):
                if X >> b & 1:
                    continue
                U, Xb = T | 1 << b, X | 1 << b
                for v in range(1, r + 1):
                    c = [-var(U, v), var(T, v), var(Xb, v), var(X, v)]
                    if v >= 2:
                        c.append(-var(X, v - 1))
                    add(c)
    add([var(mask(S), 4)])
    for i in range(N):
        add([var(mask(E[(i + t) % N] for t in range(4)), 4)])
    return cls


def canon(shape):
    """Canonical form of a gap multiset under rotation and reflection."""
    best = None
    for refl in (False, True):
        g = sorted(((-x) % N if refl else x) for x in shape)
        for rot in g:
            key = tuple(sorted((x - rot) % N for x in g))
            if best is None or key < best:
                best = key
    return best


def all_shapes():
    return sorted({canon(c) for c in itertools.combinations_with_replacement(range(N), 4)})


def shape_clauses(shape):
    out = []
    for rot in range(N):
        gs = sorted((x + rot) % N for x in shape)
        for perm in itertools.permutations(S):
            seq, gi = [], 0
            for pos in range(N):
                while gi < 4 and gs[gi] == pos:
                    seq.append(perm[gi]); gi += 1
                seq.append(E[pos])
            L = len(seq)
            lits = [-var(mask([seq[(j + t) % L] for t in range(4)]), 4) for j in range(L)
                    if any(seq[(j + t) % L] < 4 for t in range(4))]
            out.append(lits)
        # reflections are covered because all orders of S and all rotations are listed and the
        # shape set is closed under reflection by listing both mirror images below
    return out


def with_mirrors(shape):
    return {tuple(sorted(shape)), tuple(sorted((-x) % N for x in shape))}


def unsat(shapes, base_cls):
    if base_cls is None:                       # streaming mode for large N
        s = Cadical195()
        base(s.add_clause)
    else:
        s = Cadical195(bootstrap_with=base_cls)
    for sh in shapes:
        for m in with_mirrors(sh):
            for c in shape_clauses(m):
                s.add_clause(c)
    return not s.solve()


if __name__ == "__main__":
    t = time.time()
    if mode == "list":
        sh = all_shapes()
        print(len(sh), "shapes:", sh)
        sys.exit()
    B = None if "stream" in sys.argv else base()
    contiguous = (0, 0, 0, 0)
    if mode == "test":
        shapes = [contiguous] + [tuple(map(int, a.split(","))) for a in sys.argv[3:] if "," in a]
        print(f"N={N} {opts} shapes {shapes}: {'UNSAT (enough)' if unsat(shapes, B) else 'SAT'}"
              f" ({time.time() - t:.0f}s)")
    elif mode == "greedy":
        allsh = all_shapes()
        print(f"N={N} {opts}: all shapes enough: {unsat(allsh, B)}")
        chosen = list(allsh)
        for sh in list(allsh):            # drop shapes one at a time while still UNSAT
            if sh == contiguous:
                continue
            trial = [x for x in chosen if x != sh]
            if unsat(trial, B):
                chosen = trial
        print(f"  a minimal sufficient set ({len(chosen)} shapes): {chosen} ({time.time() - t:.0f}s)")
