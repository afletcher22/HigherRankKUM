"""Local re-split lemma for pair chains (rank 4), as a SAT experiment.

A pair chain is a cyclic sequence of disjoint pairs A_0 .. A_{m-1} with every A_i + A_{i+1} a
basis (van den Heuvel-Thomasse gives one for n = 4k+2, Wiedemann for n = 4k). Orient each pair as
(first, last). The windows that start inside a pair are {last(A_i)} + A_{i+1} + {first(A_{i+2})}.

R_i is the 2x2 relation {(u, v) : u in A_i, v in A_{i+2}, u + A_{i+1} + v a basis}. It has no
empty row or column (augmentation in M / A_{i+1}). If some R_i on a cycle of i -> i+2 has three
or more entries, that cycle orients. If all are permutations, the cycle orients iff the sum of
their parities has the right value; so a re-split that changes some R_i to a non-permutation, or
changes the parity sum, repairs an obstructed chain.

Local claim (12 elements, pairs Q_0 .. Q_5 = {0,1} .. {10,11}): if Q_i + Q_{i+1} are bases and
R_0 .. R_3 are permutations, then some re-split of Q_2 + Q_3 into Q_2' + Q_3' (with Q_1 + Q_2' and
Q_3' + Q_4 bases) has some new R_i' (i = 0..3) not a permutation, or a different parity sum over
R_0' .. R_3'.

mode "one": parity sum over all four (one cycle, m odd, n = 4k+2).
mode "two": the relations R_0, R_2 and R_1, R_3 lie on different cycles (m even, n = 4k); a
re-split repairs if it makes some R' a non-permutation, or changes the parity of one cycle while
keeping (or breaking into non-permutations) the other. Here we ask the weaker thing: the re-split
changes something on the bad cycle, assumed to be the cycle of R_0, R_2.

Options: simple (no parallel pairs), indepJ, caps=a,b,c (points <= a, lines <= b, planes <= c).
UNSAT proves the local claim. Usage: python localsplit.py one|two [options]
"""
import itertools, sys, time
from pysat.solvers import Cadical195

mode = sys.argv[1]
opts = sys.argv[2:]
N, r = 12, 4
var = lambda X, v: 5 * X + v
pc = lambda X: bin(X).count("1")
mask = lambda c: sum(1 << x for x in c)
Q = [(2 * i, 2 * i + 1) for i in range(6)]
nv = [5 * (1 << N) + 10]


def new():
    nv[0] += 1
    return nv[0]


indep = max([int(a[5:]) for a in opts if a.startswith("indep")], default=0)
if "simple" in opts:
    indep = max(indep, 2)
caps = next((list(map(int, a[5:].split(","))) for a in opts if a.startswith("caps=")), None)

cls = []
for X in range(1 << N):
    for v in range(1, r):
        cls.append([-var(X, v + 1), var(X, v)])
    for v in range(pc(X) + 1, r + 1):
        cls.append([-var(X, v)])
    need = 1 if pc(X) >= 1 else 0                     # no loops
    if 1 <= pc(X) <= indep:
        need = max(need, pc(X))
    if caps:
        for rank_, cap in enumerate(caps, start=1):
            if pc(X) >= cap + 1:
                need = max(need, rank_ + 1)
    if need:
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
B = lambda xs: var(mask(xs), 4)
for i in range(5):
    cls.append([B(Q[i] + Q[i + 1])])


def perm_rel(P0, P1, P2, gate=None):
    """Clauses: (gate ->) R(P0, P1, P2) is a permutation; returns its parity variable."""
    p = new()
    g = [] if gate is None else [-gate]
    for a in range(2):
        for b in range(2):
            w = B((P0[a],) + P1 + (P2[b],))
            # entry (a,b) is a basis iff (a == b) xor p (parity 0 means the diagonal)
            if a == b:
                cls.append(g + [p, w])
                cls.append(g + [-p, -w])
            else:
                cls.append(g + [-p, w])
                cls.append(g + [p, -w])
    return p


def xor_eq(bits, target, gate):
    """gate -> xor(bits) == target."""
    for vals in itertools.product((0, 1), repeat=len(bits)):
        if sum(vals) % 2 != target:
            cls.append([-gate] + [(-b if v else b) for b, v in zip(bits, vals)])


# the old relations R_0..R_3 are permutations
old = [perm_rel(Q[i], Q[i + 1], Q[i + 2]) for i in range(4)]
W = Q[2] + Q[3]
splits = []
for pair in itertools.combinations(W, 2):
    rest = tuple(x for x in W if x not in pair)
    splits.append((pair, rest))
for q2, q3 in splits:
    if set(q2) == set(Q[2]):
        continue                                   # the original split
    g = new()
    # not valid, or g (every new relation is a permutation with an unchanged parity sum)
    cls.append([-B(Q[1] + q2), -B(q3 + Q[4]), g])
    Qn = [Q[0], Q[1], q2, q3, Q[4], Q[5]]
    newp = [perm_rel(Qn[i], Qn[i + 1], Qn[i + 2], gate=g) for i in range(4)]
    if mode == "one":
        xor_eq(newp + old, 0, g)
    else:
        xor_eq([newp[0], newp[2], old[0], old[2]], 0, g)

t = time.time()
s = Cadical195(bootstrap_with=cls)
res = s.solve()
print(f"localsplit {mode} {opts}: {'SAT (a local counterexample)' if res else 'UNSAT (claim holds)'}"
      f" ({time.time() - t:.0f}s)", flush=True)
if res and "show" in opts:
    model = set(l for l in s.get_model() if l > 0)
    rk = lambda X: max([v for v in range(1, 5) if var(X, v) in model], default=0)
    for rank_ in (1, 2, 3):
        fl = []
        for X in range(1, 1 << N):
            if rk(X) == rank_ and pc(X) > rank_ and all(rk(X | 1 << e) > rank_ for e in range(N)
                                                        if not X >> e & 1):
                fl.append([e for e in range(N) if X >> e & 1])
        print(f"  nontrivial rank-{rank_} flats:", fl)
