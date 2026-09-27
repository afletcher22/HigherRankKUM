"""Structure of the matroids in which contiguous insertion fails at every gap (rank 4, N even).

Same exact encoding as xcontig.py (full rank function on N + 4 elements). The models are projected
onto their small circuits (the rank of every 2-set and 3-set) and enumerated up to relabelling S
and the dihedral symmetry of the cyclic order; each type is printed as its lines (rank-2 flats
with at least 3 elements) and parallel classes.

Usage: python xcontig_types.py N [dense|strict] [limit=K]
"""
import itertools, sys, time
from pysat.solvers import Cadical195

N = int(sys.argv[1])
opts = sys.argv[2:]
limit = next((int(a[6:]) for a in opts if a.startswith("limit=")), 10 ** 9)
n, r = N + 4, 4
var = lambda X, v: 5 * X + v
pc = lambda X: bin(X).count("1")
mask = lambda c: sum(1 << x for x in c)
S = [0, 1, 2, 3]
E = [4 + i for i in range(N)]

cls = []
for X in range(1 << n):
    for v in range(1, r):
        cls.append([-var(X, v + 1), var(X, v)])
    for v in range(pc(X) + 1, r + 1):
        cls.append([-var(X, v)])
    need = 1 if pc(X) >= 1 else 0
    if "dense" in opts or "strict" in opts:
        need = max(need, -(-4 * pc(X) // n))
        if X & 15 == 0:
            need = max(need, -(-4 * pc(X) // N))
    if "strict" in opts and 0 < pc(X) < n:
        need = max(need, 4 * pc(X) // n + 1)
    if need:
        cls.append([var(X, min(need, 4))])
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
cls.append([var(mask(S), 4)])
for i in range(N):
    cls.append([var(mask(E[(i + t) % N] for t in range(4)), 4)])
for g in range(N):
    for perm in itertools.permutations(S):
        seq = list(perm) + [E[(g + j) % N] for j in range(N)]
        L = len(seq)
        cls.append([-var(mask([seq[(j + t) % L] for t in range(4)]), 4) for j in range(L)
                    if any(seq[(j + t) % L] < 4 for t in range(4))])

pairs = list(itertools.combinations(range(n), 2))
triples = list(itertools.combinations(range(n), 3))
proj = [var(mask(p), 2) for p in pairs] + [var(mask(t), 3) for t in triples]


def sym_images():
    """Relabellings: permutations of S times dihedral maps of the cyclic order."""
    for perm in itertools.permutations(S):
        for refl in (False, True):
            for rot in range(N):
                f = {}
                for i, s in enumerate(S):
                    f[s] = perm[i]
                for i in range(N):
                    j = ((-i if refl else i) + rot) % N
                    f[E[i]] = E[j]
                yield f


SYMS = list(sym_images())
name = lambda x: "abcd"[x] if x < 4 else str(x - 4)


def small_structure(model):
    dep2 = frozenset(p for p in pairs if var(mask(p), 2) not in model)
    dep3 = frozenset(t for t in triples if var(mask(t), 3) not in model)
    return dep2, dep3


def canon(dep2, dep3):
    best = None
    for f in SYMS:
        k2 = tuple(sorted(tuple(sorted(f[x] for x in p)) for p in dep2))
        k3 = tuple(sorted(tuple(sorted(f[x] for x in t)) for t in dep3))
        key = (k2, k3)
        if best is None or key < best:
            best = key
    return best


def describe(dep2, dep3, model):
    rk = lambda X: max([v for v in range(1, 5) if var(X, v) in model], default=0)
    lines, pts = [], []
    for X in range(1, 1 << n):
        k = pc(X)
        if k >= 2 and rk(X) == 1 and all(rk(X | 1 << e) > 1 for e in range(n) if not X >> e & 1):
            pts.append(" ".join(name(e) for e in range(n) if X >> e & 1))
        if k >= 3 and rk(X) == 2 and all(rk(X | 1 << e) > 2 for e in range(n) if not X >> e & 1):
            lines.append(" ".join(name(e) for e in range(n) if X >> e & 1))
    return f"parallel classes {pts}; lines {lines}"


s = Cadical195(bootstrap_with=cls)
types = {}
t0 = time.time()
count = 0
while count < limit and s.solve():
    count += 1
    model = set(l for l in s.get_model() if l > 0)
    dep2, dep3 = small_structure(model)
    key = canon(dep2, dep3)
    if key not in types:
        types[key] = describe(dep2, dep3, model)
    # block every symmetric image of this small structure
    for f in SYMS:
        d2 = {tuple(sorted(f[x] for x in p)) for p in dep2}
        d3 = {tuple(sorted(f[x] for x in t)) for t in dep3}
        s.add_clause([(var(mask(p), 2) if p in d2 else -var(mask(p), 2)) for p in pairs] +
                     [(var(mask(t), 3) if t in d3 else -var(mask(t), 3)) for t in triples])
print(f"N={N} {opts}: {len(types)} small-circuit types where contiguous insertion fails everywhere"
      f" ({count} models, {time.time() - t0:.0f}s){' (limit reached)' if count >= limit else ''}")
for k, d in sorted(types.items(), key=lambda kv: (len(kv[0][0]), len(kv[0][1]))):
    print(" ", d)
