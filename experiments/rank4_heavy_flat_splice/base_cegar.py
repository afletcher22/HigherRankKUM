"""CEGAR SAT for base lemmas on N elements (N = 14 by default).

Claim(rho, f, caps): every rank-4 matroid on N elements that is uniformly dense, satisfies the
extra caps (max points/lines/planes), and has a flat F0 = {0..f-1} of rank rho, has a CBO
containing an F0-site.

Loop: solve (rank axioms + density + caps + F0 flat + learned 'forbid this CBO' clauses);
if UNSAT the claim holds; if SAT, extract the matroid, DFS for a site-CBO; if one is found add
the clause "some window of this order is dependent" (plus random relabellings inside F0 and
inside X0), else report a genuine counterexample.
"""
import itertools, random, sys, time
from pysat.solvers import Cadical153
from kum import Mat, is_cbo, Timeout

SITE = {3: ["1011101"], 1: ["0100010"], 2: ["100110", "011001", "010101", "101010"]}


def var(S, v):
    return S * 4 + v


def axioms(N, caps):
    cl = []
    pc = lambda S: bin(S).count("1")
    full = (1 << N) - 1
    for S in range(1 << N):
        for v in range(1, 4):
            cl.append([-var(S, v + 1), var(S, v)])
        for v in range(pc(S) + 1, 5):
            cl.append([-var(S, v)])
        need = -(-4 * pc(S) // N)
        if need >= 1:
            cl.append([var(S, need)])
    cl.append([var(full, 4)])
    for S in range(1 << N):
        for x in range(N):
            if S >> x & 1:
                continue
            T = S | 1 << x
            for v in range(1, 5):
                cl.append([-var(S, v), var(T, v)])
                if v < 4:
                    cl.append([-var(T, v + 1), var(S, v)])
            for y in range(x + 1, N):
                if S >> y & 1:
                    continue
                U, Sy = T | 1 << y, S | 1 << y
                for v in range(1, 5):
                    c = [-var(U, v), var(T, v), var(Sy, v), var(S, v)]
                    if v >= 2:
                        c.append(-var(S, v - 1))
                    cl.append(c)
    # caps: no rank-j set of size cap_j + 1
    for j, cap in enumerate(caps, start=1):
        if cap is None:
            continue
        for S in itertools.combinations(range(N), cap + 1):
            cl.append([var(sum(1 << x for x in S), j + 1)])
    return cl


def site_search(M, F0, rho, N, limit):
    """Exhaustive search for a CBO whose first positions carry a site pattern (every cyclic
    site-CBO can be rotated this way).  Returns an order, or None if none exists."""
    Fset = set(F0)
    cnt = [0]

    def okw(w):
        return M.rk(w) == len(w)

    for pat in SITE[rho]:
        order = []
        used = set()

        def dfs():
            cnt[0] += 1
            if cnt[0] > limit:
                raise Timeout
            L = len(order)
            if L == N:
                return all(okw([order[(i + j) % N] for j in range(4)]) for i in range(N - 3, N))
            need = pat[L] if L < len(pat) else None
            for e in range(N):
                if e in used:
                    continue
                if need is not None and (need == "1") != (e in Fset):
                    continue
                order.append(e)
                if okw(order[-4:] if L + 1 >= 4 else order):
                    used.add(e)
                    if dfs():
                        return True
                    used.discard(e)
                order.pop()
            return False
        if dfs():
            return list(order)
    return None


def run(rho, f, caps, N=14, max_iter=100000, relabel=8, seed=1):
    rng = random.Random(seed)
    t = time.time()
    s = Cadical153(bootstrap_with=axioms(N, caps))
    F0 = list(range(f))
    X0 = list(range(f, N))
    Fm = sum(1 << x for x in F0)
    s.add_clause([var(Fm, rho)])
    if rho < 4:
        s.add_clause([-var(Fm, rho + 1)])
    for x in X0:
        s.add_clause([var(Fm | 1 << x, rho + 1)])
    print(f"built ({time.time()-t:.0f}s)", flush=True)
    for it in range(max_iter):
        if not s.solve():
            print(f"UNSAT after {it} learned orders ({time.time()-t:.0f}s): base lemma HOLDS", flush=True)
            return True
        m = set(l for l in s.get_model() if l > 0)
        rk = lambda L: sum(1 for v in range(1, 5) if var(sum(1 << x for x in L), v) in m)
        M = Mat(N, rk)
        try:
            o = site_search(M, F0, rho, N, limit=5 * 10 ** 7)
        except Timeout:
            o = "timeout"
        if o is None:
            print(f"COUNTEREXAMPLE at iteration {it}: matroid with no site-CBO", flush=True)
            nb = [B for B in itertools.combinations(range(N), 4) if M.rk(B) < 4]
            print("non-bases:", len(nb), flush=True)
            return False
        if o == "timeout":
            print("site search timeout; stopping", flush=True)
            return None
        # forbid this order and random relabellings within F0 / X0
        for r in range(relabel + 1):
            if r == 0:
                perm = list(range(N))
            else:
                pf = F0[:]; rng.shuffle(pf)
                px = X0[:]; rng.shuffle(px)
                perm = pf + px
            oo = [perm[x] for x in o]
            wins = {sum(1 << oo[(i + j) % N] for j in range(4)) for i in range(N)}
            s.add_clause([-var(W, 4) for W in wins])
        if it % 200 == 0:
            print(f"iter {it} ({time.time()-t:.0f}s)", flush=True)
    print("max iterations reached", flush=True)
    return None


if __name__ == "__main__":
    rho, f = int(sys.argv[1]), int(sys.argv[2])
    caps = tuple(None if c == "-" else int(c) for c in sys.argv[3].split(",")) if len(sys.argv) > 3 else (None, None, None)
    run(rho, f, caps)
