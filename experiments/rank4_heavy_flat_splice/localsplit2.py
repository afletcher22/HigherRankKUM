"""Local re-split lemma for rigid pair chains (rank 4), with up to two re-splits.

A linear segment of w pairs Q_0 .. Q_{w-1} (element 2i, 2i+1 in Q_i) of a pair chain: every
Q_i + Q_{i+1} is a basis. R_i (0 <= i <= w-3) relates Q_i and Q_{i+2} through Q_{i+1}. The segment
is locally rigid if every R_i is a permutation. A re-split of window (Q_x, Q_{x+1}) changes
R_{x-2} .. R_{x+1}; it is allowed when 2 <= x <= w-4 (all changed relations inside the segment).

Claim L(w): in a locally rigid segment, some sequence of at most two allowed re-splits keeps the
chain valid and either makes some R_i not a permutation, or changes the parity sum of the R_i
(mode one: one orientation cycle, n = 4k+2), or changes the parity sum over the R_i with i even
while keeping the chain rigid-free on the odd cycle... (mode two is not implemented yet).

Rank axioms only on the subsets of each block of B consecutive pairs (weaker than a matroid on
all 2w elements, so UNSAT still proves the claim).

cyclic: the w pairs form a whole chain (indices mod w, w odd); every relation and every window
counts, and the claim is the global one (two re-splits make a rigid chain orientable), with rank
axioms on cyclic blocks of B pairs.

Usage: python localsplit2.py w B [one-move] [cyclic]
"""
import itertools, sys, time
from pysat.solvers import Cadical195

w, Bp = int(sys.argv[1]), int(sys.argv[2])
onemove = "one-move" in sys.argv
cyc = "cyclic" in sys.argv
N, r = 2 * w, 4
var = lambda X, v: 5 * X + v
pc = lambda X: bin(X).count("1")
mask = lambda c: sum(1 << x for x in c)
Q = [(2 * i, 2 * i + 1) for i in range(w)]
nv = [5 * (1 << N) + 10]


def new():
    nv[0] += 1
    return nv[0]


cls, seen = [], set()


def add(c):
    t = tuple(c)
    if t not in seen:
        seen.add(t)
        cls.append(c)


done = set()
for start in (range(w) if cyc else range(0, w - Bp + 1)):
    blk = sorted(e for i in range(start, start + Bp) for e in Q[i % w])
    subs = [mask(c) for k in range(len(blk) + 1) for c in itertools.combinations(blk, k)]
    for X in subs:
        if X in done:
            continue
        done.add(X)
        for v in range(1, r):
            add([-var(X, v + 1), var(X, v)])
        for v in range(pc(X) + 1, r + 1):
            add([-var(X, v)])
        if pc(X) >= 1:
            add([var(X, 1)])
    for X in subs:
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
Bs = lambda xs: var(mask(xs), 4)
for i in range(w if cyc else w - 1):
    add([Bs(Q[i] + Q[(i + 1) % w])])


def perm_rel(P0, P1, P2, gate=None):
    p = new()
    g = [] if gate is None else [-gate]
    for a in range(2):
        for b in range(2):
            x = Bs((P0[a],) + P1 + (P2[b],))
            if a == b:
                add(g + [p, x]); add(g + [-p, -x])
            else:
                add(g + [-p, x]); add(g + [p, -x])
    return p


def xor_eq(bits, target, gate):
    for vals in itertools.product((0, 1), repeat=len(bits)):
        if sum(vals) % 2 != target:
            add([-gate] + [(-b if v else b) for b, v in zip(bits, vals)])


nrel = w if cyc else w - 2
old = [perm_rel(Q[i], Q[(i + 1) % w], Q[(i + 2) % w]) for i in range(nrel)]
if cyc:
    # rigid: the parity sum of all relations has the non-orientable value (w odd: one cycle)
    top = new()
    add([top])
    xor_eq(old, 0, top)    # parity convention: sum 0 is the rigid value up to a global flip


def resplits(ch):
    for x in (range(w) if cyc else range(2, w - 3)):
        W = ch[x] + ch[(x + 1) % w]
        for q in itertools.combinations(W, 2):
            if set(q) == set(ch[x]):
                continue
            c2 = list(ch)
            c2[x], c2[(x + 1) % w] = q, tuple(y for y in W if y not in q)
            yield x, c2


cands = []
for x, c1 in resplits(Q):
    cands.append(([x], [c1]))
    if not onemove:
        for y, c2 in resplits(c1):
            cands.append(([x, y], [c1, c2]))
for xs, chs in cands:
    g = new()
    valid = []
    prev = Q
    for x, ch in zip(xs, chs):
        valid += [Bs(ch[(x - 1) % w] + ch[x]), Bs(ch[(x + 1) % w] + ch[(x + 2) % w])]
    add([-v for v in valid] + [g])
    fin = chs[-1]
    newp = [perm_rel(fin[i], fin[(i + 1) % w], fin[(i + 2) % w], gate=g) for i in range(nrel)]
    xor_eq(newp + old, 0, g)

t = time.time()
s = Cadical195(bootstrap_with=cls)
res = s.solve()
print(f"L(w={w}, blocks of {Bp} pairs{', one move' if onemove else ''}): "
      f"{'SAT (local counterexample)' if res else 'UNSAT (lemma holds)'}; {len(cls)} clauses, "
      f"{len(cands)} candidates ({time.time() - t:.0f}s)", flush=True)
