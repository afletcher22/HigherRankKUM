"""The hitting lemma at n=14 (k=3), 6-line case, as a canonical tagged formula for Lean.

Claim (hit_sat14_split.py line): every strict t=0 rank-4 matroid on 14 elements in which {0..5}
has rank 2 and no plane has 9 elements has a basis B whose complement is uniformly dense.
Variable 4X+v means r(X) >= v.

* rank axioms on all 2^14 subsets (tags o c m i s, as in lean_witness.py);
* one lower-bound clause per set from the size table LOW14 (tag l): no loops, points <= 3,
  lines <= 6, and no 9-plane;
* the facts r({0..5}) >= 2 and r({0..5}) < 3 (tag f);
* for every 4-set B (tag h B), the clause
      -(B,4) | -(Y,2) for 3-sets Y of E-B | -(Y,3) for 6-sets | -(Y,4) for 8-sets,
  the sets Y listed in itertools.combinations order of E-B (increasing positions), which is the
  order of `combs` on the Lean side.

The formula is solved with CaDiCaL LRAT (lrat_native), trimmed, checked, and written to
OUTDIR/hit14line.{cnf,lrat,wit}.

Usage: python lean_witness_h.py OUTDIR NAME...   (hit14line, hit14g, hit14light)
"""
import itertools, json, os, sys, time
from cert_measure import OUT
from lrat_native import solve_lrat, trim
from lrat_check import check as lrat_check

N = 14
LOW14 = [0, 1, 1, 1, 2, 2, 2, 3, 3, 4, 4, 4, 4, 4, 4]     # 6-line case: no 9-plane
LOWG = [0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 4, 4]      # 9-plane case: planes <= 9
LOWL = [0, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 4, 4, 4, 4]      # Lemma H case: lines <= 5, planes <= 8


def var(X, v):
    return 4 * X + v


def mask(xs):
    return sum(1 << x for x in xs)


def rank_axioms(low):
    pc = lambda X: bin(X).count("1")
    for X in range(1 << N):
        for v in range(1, 4):
            yield [-var(X, v + 1), var(X, v)], ("o", X, v)
        for v in range(pc(X) + 1, 5):
            yield [-var(X, v)], ("c", X, v)
        if low[pc(X)] >= 1:
            yield [var(X, low[pc(X)])], ("l", X, low[pc(X)])
    for X in range(1 << N):
        for a in range(N):
            if X >> a & 1:
                continue
            T = X | 1 << a
            for v in range(1, 5):
                yield [-var(X, v), var(T, v)], ("m", X, a, v)
                if v < 4:
                    yield [-var(T, v + 1), var(X, v)], ("i", X, a, v)
            for b in range(a + 1, N):
                if X >> b & 1:
                    continue
                U, Xb = T | 1 << b, X | 1 << b
                for v in range(1, 5):
                    c = [-var(U, v), var(T, v), var(Xb, v), var(X, v)]
                    if v >= 2:
                        c.append(-var(X, v - 1))
                    yield c, ("s", X, a, b, v)


def hit_clause(B):
    rest = [x for x in range(N) if not B >> x & 1]
    c = [-var(B, 4)]
    c += [-var(mask(Y), 2) for Y in itertools.combinations(rest, 3)]
    c += [-var(mask(Y), 3) for Y in itertools.combinations(rest, 6)]
    c += [-var(mask(Y), 4) for Y in itertools.combinations(rest, 8)]
    return c, ("h", B)


def claim(name):
    """(size table, facts, candidate 4-sets) of a claim."""
    if name == "hit14line":
        L = mask(range(6))
        return LOW14, [(L, 2, 1), (L, 3, 0)], [mask(Bt) for Bt in itertools.combinations(range(N), 4)]
    if name == "hit14g":
        K = mask(range(9))
        D = [mask(range(3 * i, 3 * i + 3)) for i in range(3)]
        facts = [(K, 3, 1), (K, 4, 0)] + [f for Di in D for f in [(Di, 3, 1), (Di, 4, 0)]]
        cands = [Di | 1 << z for Di in D for z in range(9, N)]
        return LOWG, facts, cands
    if name == "hit14light":
        return LOWL, [], [mask(Bt) for Bt in itertools.combinations(range(N), 4)]
    raise ValueError(name)


def run(outdir, name):
    t0 = time.time()
    low, facts, cands = claim(name)
    cls, tags = [], []
    for c, t in rank_axioms(low):
        cls.append(c); tags.append(t)
    for X, v, b in facts:
        cls.append([var(X, v)] if b else [-var(X, v)]); tags.append(("f", X, v, b))
    for B in cands:
        c, t = hit_clause(B)
        cls.append(c); tags.append(t)
    raw = os.path.join(OUT, f"{name}.h.native.lrat")
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
    nv = 4 * ((1 << N) - 1) + 4
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, f"{name}.cnf"), "w", newline="\n") as f:
        f.write(f"p cnf {nv} {len(core)}\n")
        for c in core:
            f.write(" ".join(map(str, c)) + " 0\n")
    with open(os.path.join(outdir, f"{name}.lrat"), "w", newline="\n") as f:
        f.write("\n".join(lines) + "\n")
    with open(os.path.join(outdir, f"{name}.wit"), "w", newline="\n") as f:
        for i in used:
            f.write(" ".join(map(str, tags[i - 1])) + "\n")
    ok, msg = lrat_check(core, lines)
    kinds = {}
    for i in used:
        kinds[tags[i - 1][0]] = kinds.get(tags[i - 1][0], 0) + 1
    os.remove(raw)
    print(json.dumps({"name": name, "clauses": m, "core": len(core), "steps": len(keep),
                      "hints": sum(len(steps[s][1]) for s in keep), "kinds": kinds,
                      "check": ("VERIFIED " if ok else "REJECTED ") + msg,
                      "seconds": round(time.time() - t0)}), flush=True)


if __name__ == "__main__":
    for nm in sys.argv[2:]:
        run(sys.argv[1], nm)
