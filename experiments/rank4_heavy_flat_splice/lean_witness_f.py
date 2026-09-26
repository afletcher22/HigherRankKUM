"""Canonical tagged formulas for the n=10 claims, certified with CaDiCaL LRAT, exported for Lean.

The five claims that rank-4 KUM on 10 elements (strict, t=0) needs. N = 10; variable 4X+v means
r(X) >= v for a bitmask X.

  baseG2, baseG3, baseG4  the base lemma of Theorem G (base_sat.py): a 6-point plane K = {0..5},
                          C = {6..9} with r(C) = 2, 3 or 4; one clause per site order
  baseL4                  the base lemma of Theorem L4 (base_sat_general.py 2 4): a 4-point line
                          F = {0..3}; one clause per site order
  kum10l                  strict t=0 with no 6-plane and no 4-line: the size table LIGHT bounds
                          every rank from below; one clause per cyclic order (0 first, one of each
                          reflection pair)

The formulas are the same claims as the scripts above, re-emitted in a canonical form:

* the rank axioms of lean_witness.py, with one lower-bound clause per set;
* window clauses listing the 10 windows of the order in order, not as a set.

Witness tokens: o c m i s as in lean_witness.py, and
  l X v          [(X,v)]                    v <= LOW[|X|]
  f X v b        [(X,v)] if b else [-(X,v)]  (X, v, b) is one of the claim's FACTS
  w s0 .. s9     [-(W_0,4), ..., -(W_9,4)]   s is a permutation of 0..9

The formula is solved (lrat_native.solve_lrat), trimmed, and written to OUTDIR/NAME.{cnf,lrat,wit};
the facts are printed as a Lean list for the certificate module.

Usage: python lean_witness_f.py OUTDIR NAME...
"""
import itertools, json, os, sys, time
from base_sat import SHAPES
from base_sat_general import SITE, has_site
from cert_measure import OUT
from lrat_native import solve_lrat, trim
from lrat_check import check as lrat_check

N = 10
DENS = [-(-4 * s // N) for s in range(N + 1)]             # r(X) >= ceil(4|X|/10)
LIGHT = [0, 1, 1, 2, 3, 3, 4, 4, 4, 4, 4]                  # strict t=0, no 6-plane, no 4-line


def var(X, v):
    return 4 * X + v


def mask(xs):
    return sum(1 << x for x in xs)


def rank_axioms(low):
    pc = lambda X: bin(X).count("1")
    out = []
    for X in range(1 << N):
        for v in range(1, 4):
            out.append(([-var(X, v + 1), var(X, v)], ("o", X, v)))
        for v in range(pc(X) + 1, 5):
            out.append(([-var(X, v)], ("c", X, v)))
        if low[pc(X)] >= 1:
            out.append(([var(X, low[pc(X)])], ("l", X, low[pc(X)])))
    for X in range(1 << N):
        for a in range(N):
            if X >> a & 1:
                continue
            T = X | 1 << a
            for v in range(1, 5):
                out.append(([-var(X, v), var(T, v)], ("m", X, a, v)))
                if v < 4:
                    out.append(([-var(T, v + 1), var(X, v)], ("i", X, a, v)))
            for b in range(a + 1, N):
                if X >> b & 1:
                    continue
                U, Xb = T | 1 << b, X | 1 << b
                for v in range(1, 5):
                    c = [-var(U, v), var(T, v), var(Xb, v), var(X, v)]
                    if v >= 2:
                        c.append(-var(X, v - 1))
                    out.append((c, ("s", X, a, b, v)))
    return out


def fix_rank(X, r):
    """Facts saying r(X) = r."""
    out = []
    if r >= 1:
        out.append((X, r, 1))
    if r < 4:
        out.append((X, r + 1, 0))
    return out


def window_clause(seq):
    return ([-var(mask(seq[(i + j) % N] for j in range(4)), 4) for i in range(N)], ("w",) + tuple(seq))


def site_orders_G():
    K, C = list(range(6)), list(range(6, 10))
    for sh in SHAPES:
        for ko in itertools.permutations(K):
            for co in itertools.permutations(C):
                seq, ki, ci = [], 0, 0
                for s in sh:
                    if s == "K":
                        seq.append(ko[ki]); ki += 1
                    else:
                        seq.append(co[ci]); ci += 1
                yield seq


def site_orders_general(rho, f):
    F, X = list(range(f)), list(range(f, N))
    for pos in itertools.combinations(range(1, N), f - 1):
        fpos = (0,) + pos
        bits = "".join("1" if i in fpos else "0" for i in range(N))
        if not has_site(bits, rho):
            continue
        for fo in itertools.permutations(F[1:]):
            forder = (F[0],) + fo
            for xo in itertools.permutations(X):
                seq, fi, xi = [], 0, 0
                for b in bits:
                    if b == "1":
                        seq.append(forder[fi]); fi += 1
                    else:
                        seq.append(xo[xi]); xi += 1
                yield seq


def all_orders():
    for rest in itertools.permutations(range(1, N)):
        if rest[0] > rest[-1]:
            continue
        yield (0,) + rest


def claim(name):
    """(low table, facts, orders) of a claim."""
    if name.startswith("baseG"):
        rC = int(name[5:])
        Km, Cm = mask(range(6)), mask(range(6, 10))
        facts = fix_rank(Km, 3) + [(Km | 1 << c, 4, 1) for c in range(6, 10)] + fix_rank(Cm, rC)
        return DENS, facts, site_orders_G()
    if name == "baseL4":
        Fm = mask(range(4))
        facts = fix_rank(Fm, 2)
        for x in range(4, N):
            facts += fix_rank(Fm | 1 << x, 3)
        return DENS, facts, site_orders_general(2, 4)
    if name == "kum10l":
        return LIGHT, [], all_orders()
    raise ValueError(name)


def build(name):
    low, facts, orders = claim(name)
    tagged = rank_axioms(low)
    for X, v, b in facts:
        tagged.append(([var(X, v)] if b else [-var(X, v)], ("f", X, v, b)))
    seen = set()
    for seq in orders:
        c, tag = window_clause(seq)
        if tag in seen:
            continue
        seen.add(tag)
        tagged.append((c, tag))
    return tagged, facts


def run(outdir, name):
    t0 = time.time()
    tagged, facts = build(name)
    cls = [c for c, _ in tagged]
    raw = os.path.join(OUT, f"{name}.f.native.lrat")
    solve_lrat(cls, raw)
    m = len(cls)
    keep, steps, used, orig = trim(m, raw)
    newidx = {old: new for new, old in enumerate(used, 1)}
    cid, nxt = {}, len(used)
    for sid in keep:
        nxt += 1
        cid[sid] = nxt
    ref = lambda h: newidx[orig[h]] if h in orig else cid[h]
    lines = [f"{cid[s]} {' '.join(map(str, steps[s][0]))} 0 {' '.join(str(ref(h)) for h in steps[s][1])} 0"
             for s in keep]
    core = [cls[i - 1] for i in used]
    nv = max(abs(l) for c in cls for l in c)
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, f"{name}.cnf"), "w", newline="\n") as f:
        f.write(f"p cnf {nv} {len(core)}\n")
        for c in core:
            f.write(" ".join(map(str, c)) + " 0\n")
    with open(os.path.join(outdir, f"{name}.lrat"), "w", newline="\n") as f:
        f.write("\n".join(lines) + "\n")
    with open(os.path.join(outdir, f"{name}.wit"), "w", newline="\n") as f:
        for i in used:
            f.write(" ".join(map(str, tagged[i - 1][1])) + "\n")
    ok, msg = lrat_check(core, lines)
    kinds = {}
    for i in used:
        kinds[tagged[i - 1][1][0]] = kinds.get(tagged[i - 1][1][0], 0) + 1
    os.remove(raw)
    rec = {"name": name, "clauses": m, "core": len(core), "steps": len(keep),
           "hints": sum(len(steps[s][1]) for s in keep), "kinds": kinds,
           "check": ("VERIFIED " if ok else "REJECTED ") + msg, "seconds": round(time.time() - t0),
           "facts_lean": "[" + ", ".join(f"({X}, {v}, {'true' if b else 'false'})"
                                         for X, v, b in facts) + "]"}
    print(json.dumps(rec), flush=True)


if __name__ == "__main__":
    outdir = sys.argv[1]
    for nm in sys.argv[2:]:
        run(outdir, nm)
