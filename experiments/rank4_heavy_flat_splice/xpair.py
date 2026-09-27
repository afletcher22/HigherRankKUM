"""X' at the level of pair chains (rank 4), exact encoding.

sigma = e_0 .. e_{N-1} (N even) is a cyclic basis ordering of M - S, S a basis. Its pairs
A_i = {e_{2i}, e_{2i+1}} form an orientable pair chain; so do the shifted pairs
A'_i = {e_{2i+1}, e_{2i+2}}. Split S into an ordered pair of pairs (P, Q) and insert them between
A_j and A_{j+1} of one of the two pairings: the chain ..., A_j, P, Q, A_{j+1}, ... is valid when
A_j + P and Q + A_{j+1} are bases (P + Q = S is). Claim XP(N): some valid new chain is orientable
(every pair, old or new, may be flipped).

With the option "fixed", old pairs keep their orientation from sigma (that is exactly contiguous
insertion of S at an even gap, for comparison).

j=J: only insertion position J (repeatable).

tight: sigma's pair chain is tight (every relation a permutation).
block=W: rank axioms only on S + W consecutive pairs (cyclically); UNSAT is still a proof.

Usage: python xpair.py N [fixed] [noshift] [j=J] [block=W] [dense|strict]
"""
import itertools, sys, time
from pysat.solvers import Cadical195

N = int(sys.argv[1])
opts = sys.argv[2:]
n, r = N + 4, 4
var = lambda X, v: 5 * X + v
pc = lambda X: bin(X).count("1")
mask = lambda c: sum(1 << x for x in c)
S = [0, 1, 2, 3]
E = [4 + i for i in range(N)]
s = Cadical195()
add = s.add_clause

blockw = next((int(a[6:]) for a in opts if a.startswith("block=")), None)
if blockw is None:
    universe = range(1 << n)
    pairsets = None
else:
    # rank axioms only on the subsets of S + (blockw consecutive pairs of sigma), cyclically
    universe = set()
    for st in range(0, N, 2):
        blk = S + [E[(st + t) % N] for t in range(2 * blockw)]
        for k in range(len(blk) + 1):
            for c in itertools.combinations(blk, k):
                universe.add(mask(c))
    universe = sorted(universe)
    blocks = []
    for st in range(0, N, 2):
        blocks.append(set(S + [E[(st + t) % N] for t in range(2 * blockw)]))
inU = (lambda X: True) if blockw is None else (lambda X, U=set(universe): X in U)
for X in universe:
    for v in range(1, r):
        add([-var(X, v + 1), var(X, v)])
    for v in range(pc(X) + 1, r + 1):
        add([-var(X, v)])
    need = 1 if pc(X) >= 1 else 0
    if "dense" in opts or "strict" in opts:
        need = max(need, -(-4 * pc(X) // n))
        if X & 15 == 0:
            need = max(need, -(-4 * pc(X) // N))
    if "strict" in opts and 0 < pc(X) < n:
        need = max(need, 4 * pc(X) // n + 1)
    if need:
        add([var(X, min(need, 4))])
for X in universe:
    for a in range(n):
        if X >> a & 1:
            continue
        T = X | 1 << a
        if not inU(T):
            continue
        for v in range(1, r + 1):
            add([-var(X, v), var(T, v)])
            if v < r:
                add([-var(T, v + 1), var(X, v)])
        for b in range(a + 1, n):
            if X >> b & 1:
                continue
            U, Xb = T | 1 << b, X | 1 << b
            if not inU(U):
                continue
            for v in range(1, r + 1):
                c = [-var(U, v), var(T, v), var(Xb, v), var(X, v)]
                if v >= 2:
                    c.append(-var(X, v - 1))
                add(c)
add([var(mask(S), 4)])
for i in range(N):
    add([var(mask(E[(i + t) % N] for t in range(4)), 4)])
B = lambda xs: var(mask(xs), 4)

if "tight" in opts:
    # every relation R_i of sigma's pairs (A_i -> A_{i+2} through A_{i+1}) is a permutation:
    # sigma gives (last A_i, first A_{i+2}); so (first A_i, last A_{i+2}) is an entry too and
    # (last, last), (first, first) are not
    A0 = [(E[2 * i], E[2 * i + 1]) for i in range(N // 2)]
    m0 = len(A0)
    for i in range(m0):
        a, ab = A0[i]
        c, cb = A0[(i + 2) % m0]
        mid = A0[(i + 1) % m0]
        add([B((a,) + mid + (cb,))])
        add([-B((ab,) + mid + (cb,))])
        add([-B((a,) + mid + (c,))])
splits = []
for P in itertools.combinations(S, 2):
    Q = tuple(x for x in S if x not in P)
    splits.append((P, Q))
pairings = [0] if "noshift" in opts else [0, 1]
ncand = 0
for sh in pairings:
    A = [(E[(2 * i + sh) % N], E[(2 * i + 1 + sh) % N]) for i in range(N // 2)]
    m = len(A)
    jlist = range(m)
    if any(a.startswith("j=") for a in opts):
        jlist = [int(a[2:]) for a in opts if a.startswith("j=")]
    for j in jlist:
        for P, Q in splits:
            chain = A[:j + 1] + [P, Q] + A[j + 1:]
            L = len(chain)
            # valid -> not orientable: for every orientation, some shifted window fails
            valid = [B(A[j] + P), B(Q + A[(j + 1) % m])]
            if "fixed" in opts:
                orients = []
                for oP in range(2):
                    for oQ in range(2):
                        o = [0] * L
                        o[j + 1], o[j + 2] = oP, oQ
                        orients.append(o)
            else:
                orients = itertools.product((0, 1), repeat=L)
            for o in orients:
                first = [chain[i][o[i]] for i in range(L)]
                last = [chain[i][1 - o[i]] for i in range(L)]
                add([-v for v in valid] +
                    [-B((last[i],) + chain[(i + 1) % L] + (first[(i + 2) % L],)) for i in range(L)])
            ncand += 1
t = time.time()
res = s.solve()
print(f"XP({N}) {opts}: {'SAT (can fail)' if res else 'UNSAT (holds)'}; {ncand} candidate chains "
      f"({time.time() - t:.0f}s)", flush=True)
