"""Pair chains from van den Heuvel-Thomasse at n = 4k+2 (rank 4).

vHT Theorem 2.1 with arc weight 2 on Z_{2k+1} splits a uniformly dense rank-4 matroid on 4k+2
elements into pairs P_0 .. P_{2k} with every P_i + P_{i+1} a basis. Here P_i = {2i, 2i+1}.

* orientable: some order a_0 b_0 a_1 b_1 ... (each P_i oriented) is a cyclic basis ordering; the
  only new windows are {b_i} + P_{i+1} + {a_{i+2}}.
* pair deletion: some P_{i-1} + P_{i+2} is a basis; then S = P_i + P_{i+1} is deletable (the
  2k-1 remaining pairs form a chain, hence a double cover of M - S).

Question: is there a matroid with a chain that is rigid (no orientation works) and has no pair
deletion? Options: strict (strict t=0 caps: points <= k, lines <= 2k, planes <= 3k),
nodel (no pair deletion), rigid (no orientation).

resplit2: also every sequence of two re-splits is rigid (implies resplit's variables).
resplit: also every single re-split of a window A_x + A_{x+1} (into two other pairs, keeping the
chain valid) is rigid.

div: n = 4k with a chain of 2k pairs (Wiedemann's circular exchange theorem gives one, with the
split of the first basis prescribed); the orientation cycles i -> i+2 are then two, not one.

write: also write certs/pairchainN_OPTS.cnf (for lrat_native.py).

Usage: python pairchain.py k [div] [strict] [rigid] [nodel] [resplit] [write] [show]
"""
import itertools, sys, time
from pysat.solvers import Cadical195

k = int(sys.argv[1])
opts = set(sys.argv[2:])
if "div" in opts:                                   # n = 4k, a Wiedemann chain of 2k pairs
    N, r = 4 * k, 4
    m = 2 * k
else:
    N, r = 4 * k + 2, 4
    m = 2 * k + 1
var = lambda X, v: 5 * X + v
pc = lambda X: bin(X).count("1")
mask = lambda c: sum(1 << x for x in c)
P = [(2 * i, 2 * i + 1) for i in range(m)]

cls = []
for X in range(1 << N):
    for v in range(1, r):
        cls.append([-var(X, v + 1), var(X, v)])
    for v in range(pc(X) + 1, r + 1):
        cls.append([-var(X, v)])
    need = -(-r * pc(X) // N)                       # uniform density
    if "strict" in opts:
        caps = {1: 1, k + 1: 2, 2 * k + 1: 3, 3 * k + 1: 4}
        need = max([need] + [v for s, v in caps.items() if pc(X) >= s])
    if need >= 1:
        cls.append([var(X, min(need, r))])
for X in range(1 << N):
    for a in range(N):
        if X >> a & 1:
            continue
        T = X | 1 << a
        for v in range(1, r + 1):
            cls.append([-var(X, v), var(T, v)])
            if v < r:
                cls.append([-var(T, v + 1), var(X, v)])
        for b in range(a + 1, N):
            if X >> b & 1:
                continue
            U, Xb = T | 1 << b, X | 1 << b
            for v in range(1, r + 1):
                c = [-var(U, v), var(T, v), var(Xb, v), var(X, v)]
                if v >= 2:
                    c.append(-var(X, v - 1))
                cls.append(c)
for i in range(m):
    cls.append([var(mask(P[i] + P[(i + 1) % m]), 4)])
if "rigid" in opts:
    for s in itertools.product((0, 1), repeat=m):
        first = [P[i][s[i]] for i in range(m)]
        last = [P[i][1 - s[i]] for i in range(m)]
        cls.append([-var(mask((last[i],) + P[(i + 1) % m] + (first[(i + 2) % m],)), 4)
                    for i in range(m)])
def rigid_gated(chain, gate):
    for s_ in itertools.product((0, 1), repeat=m):
        first = [chain[i][s_[i]] for i in range(m)]
        last = [chain[i][1 - s_[i]] for i in range(m)]
        cls.append([-gate] + [-var(mask((last[i],) + chain[(i + 1) % m] + (first[(i + 2) % m],)), 4)
                              for i in range(m)])


nv = 5 * (1 << N) + 10
if "resplit" in opts:
    # every single re-split of a window A_x + A_{x+1} gives an invalid chain or a rigid one
    for x in range(m):
        W = P[x] + P[(x + 1) % m]
        for q2 in itertools.combinations(W, 2):
            q3 = tuple(y for y in W if y not in q2)
            if set(q2) == set(P[x]):
                continue
            chain = list(P)
            chain[x], chain[(x + 1) % m] = q2, q3
            nv += 1
            cls.append([-var(mask(P[(x - 1) % m] + q2), 4), -var(mask(q3 + P[(x + 2) % m]), 4), nv])
            rigid_gated(chain, nv)
if "resplit2" in opts:
    # also every pair of re-splits (two different windows, applied in sequence) gives an invalid
    # chain or a rigid one
    def resplits(ch):
        for x in range(m):
            W = ch[x] + ch[(x + 1) % m]
            for q2 in itertools.combinations(W, 2):
                q3 = tuple(y for y in W if y not in q2)
                if set(q2) == set(ch[x]):
                    continue
                c2 = list(ch)
                c2[x], c2[(x + 1) % m] = q2, q3
                yield x, c2
    seen = set()
    for x, c1 in resplits(P):
        for y, c2 in resplits(c1):
            key = tuple(tuple(sorted(q)) for q in c2)
            if key in seen or key == tuple(P):
                continue
            seen.add(key)
            nv += 1
            valid = [var(mask(c1[(x - 1) % m] + c1[x]), 4), var(mask(c1[(x + 1) % m] + c1[(x + 2) % m]), 4),
                     var(mask(c2[(y - 1) % m] + c2[y]), 4), var(mask(c2[(y + 1) % m] + c2[(y + 2) % m]), 4)]
            cls.append([-v for v in valid] + [nv])
            rigid_gated(c2, nv)
if "nodel" in opts:
    for i in range(m):
        cls.append([-var(mask(P[(i - 1) % m] + P[(i + 2) % m]), 4)])

if "write" in opts:
    import os
    from cert_measure import OUT
    name = "pairchain" + str(N) + "_" + "_".join(sorted(o for o in opts if o != "write"))
    with open(os.path.join(OUT, name + ".cnf"), "w", newline="\n") as f:
        f.write(f"p cnf {max(abs(l) for c in cls for l in c)} {len(cls)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    print("wrote", name, len(cls), "clauses")
t = time.time()
s = Cadical195(bootstrap_with=cls)
res = s.solve()
print(f"k={k} {sorted(opts)}: {'SAT' if res else 'UNSAT'} ({time.time() - t:.0f}s)", flush=True)
if res and "show" in opts:
    model = set(l for l in s.get_model() if l > 0)
    rk = lambda X: max([v for v in range(1, 5) if var(X, v) in model], default=0)
    for sz, lab in ((2, "points"), (3, "lines"), (4, "planes")):
        pass
    deps = [c for c in itertools.combinations(range(N), 4) if rk(mask(c)) < 4]
    print("non-bases:", len(deps))
    for c in deps:
        print(" ", c, rk(mask(c)))
    for rank_ in (1, 2, 3):
        fl = []
        for X in range(1, 1 << N):
            if rk(X) == rank_ and all(rk(X | 1 << e) > rank_ for e in range(N) if not X >> e & 1):
                if pc(X) > rank_:
                    fl.append([e for e in range(N) if X >> e & 1])
        print(f"nontrivial rank-{rank_} flats:", fl)
