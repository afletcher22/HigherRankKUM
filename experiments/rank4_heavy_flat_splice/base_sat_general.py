"""General 10-element base lemmas by SAT (representation-free).

Base: rank-4 matroid M0 on 10 elements, uniformly dense (4|S| <= 10 r(S)), with a flat F0 of
rank rho and size f.  Claim: M0 has a CBO containing an F-site:
    rho=3: F-pattern 1011101;  rho=1: 0100010;  rho=2: 100110, 011001, 010101 or 101010.
UNSAT of (rank axioms + density + F0 flat + "no CBO contains a site") proves the claim.

Usage: python base_sat_general.py RHO F
"""
import itertools, sys, time
from pysat.solvers import Cadical153

N = 10
FULL = (1 << N) - 1
SITE = {3: ["1011101"], 1: ["0100010"], 2: ["100110", "011001", "010101", "101010"]}


def var(S, v):
    return S * 4 + v


def rank_axioms():
    cl = []
    pc = lambda S: bin(S).count("1")
    for S in range(1 << N):
        for v in range(1, 4):
            cl.append([-var(S, v + 1), var(S, v)])
        for v in range(pc(S) + 1, 5):
            cl.append([-var(S, v)])
        need = -(-4 * pc(S) // 10)
        if need >= 1:
            cl.append([var(S, need)])
    cl.append([var(FULL, 4)])
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
    return cl


def fix_rank(S, r):
    out = []
    if r >= 1:
        out.append([var(S, r)])
    if r < 4:
        out.append([-var(S, r + 1)])
    return out


def has_site(bits, rho):
    s = bits + bits
    return any(p in s for p in SITE[rho])


def build(rho, f):
    F = list(range(f))
    X = list(range(f, N))
    Fm = sum(1 << x for x in F)
    cl = rank_axioms()
    cl += fix_rank(Fm, rho)
    for x in X:
        cl += fix_rank(Fm | 1 << x, rho + 1)          # F0 is a flat of rank rho
    nsite = 0
    for pos in itertools.combinations(range(1, N), f - 1):
        fpos = (0,) + pos                              # an F element at position 0 (rotation)
        bits = "".join("1" if i in fpos else "0" for i in range(N))
        if not has_site(bits, rho):
            continue
        for fo in itertools.permutations(F[1:]):       # F[0] at position 0 (label symmetry of rotation)
            forder = (F[0],) + fo
            for xo in itertools.permutations(X):
                seq, fi, xi = [], 0, 0
                for b in bits:
                    if b == "1":
                        seq.append(forder[fi]); fi += 1
                    else:
                        seq.append(xo[xi]); xi += 1
                wins = {sum(1 << seq[(i + j) % N] for j in range(4)) for i in range(N)}
                cl.append([-var(W, 4) for W in wins])
                nsite += 1
    return cl, nsite


if __name__ == "__main__":
    rho, f = int(sys.argv[1]), int(sys.argv[2])
    t = time.time()
    cl, ns = build(rho, f)
    s = Cadical153(bootstrap_with=cl)
    res = s.solve()
    print(f"rho={rho} |F0|={f}: clauses={len(cl)} site-sequences={ns} -> "
          f"{'SAT (base lemma FAILS)' if res else 'UNSAT (base lemma holds)'} ({time.time()-t:.0f}s)", flush=True)
    if res:
        m = set(l for l in s.get_model() if l > 0)
        r = lambda S: sum(1 for v in range(1, 5) if var(S, v) in m)
        nb = [B for B in itertools.combinations(range(N), 4) if r(sum(1 << x for x in B)) < 4]
        print("non-bases (4-sets):", nb)
