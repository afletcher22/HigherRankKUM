"""Export a core-restricted certificate plus per-clause witnesses for the Lean encoding layer.

The KUM formulas of certify.kum_formula(N) use the variable 4X+v for "r(X) >= v", with X a
bitmask over the N elements and 1 <= v <= 4.  This script regenerates that formula with a tag for
every clause, checks it is identical to certify.formula(NAME), and then, for the formula clauses
used by certs/NAME.lrat (the trimmed LRAT from lrat_emit.py), writes:

  probes/data/NAME.cnf   core CNF with the ORIGINAL variable numbers
  probes/data/NAME.lrat  LRAT proof renumbered to the core
  probes/data/NAME.wit   one witness per core clause, in order

Witness tokens (the Lean side regenerates each clause from its witness):
  o X v        order          [-(X,v+1), (X,v)]
  c X v        cap            [-(X,v)]                v > |X|
  d X k        density        [(X,k)]                 N(k-1) < 4|X|
  m X a v      monotone       [-(X,v), (X+a,v)]
  i X a v      unit increase  [-(X+a,v+1), (X,v)]
  s X a b v    submodular     [-(X+a+b,v), (X+a,v), (X+b,v), (X,v)] (+ [-(X,v-1)] if v >= 2)
  w s0 .. sN-1 window         [-(W_0,4), ..., -(W_{N-1},4)] for the cyclic sequence s

Usage: python lean_witness.py NAME...   (NAME in kum6, kum8)
"""
import itertools, os, sys
from certify import formula
from cert_measure import OUT
from lrat_emit import read_dimacs

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))


def kum_tagged(N):
    var = lambda X, v: X * 4 + v
    pc = lambda X: bin(X).count("1")
    out = []
    for X in range(1 << N):
        for v in range(1, 4):
            out.append(([-var(X, v + 1), var(X, v)], ("o", X, v)))
        for v in range(pc(X) + 1, 5):
            out.append(([-var(X, v)], ("c", X, v)))
        need = -(-4 * pc(X) // N)
        if need >= 1:
            assert need <= 4
            out.append(([var(X, need)], ("d", X, need)))
    out.append(([var((1 << N) - 1, 4)], ("d", (1 << N) - 1, 4)))
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
    for rest in itertools.permutations(range(1, N)):
        if rest[0] > rest[-1]:
            continue
        seq = (0,) + rest
        out.append(([-var(sum(1 << seq[(i + j) % N] for j in range(4)), 4) for i in range(N)],
                    ("w",) + seq))
    return out


def export(name):
    N = {"kum6": 6, "kum8": 8}[name]
    tagged = kum_tagged(N)
    plain = formula(name)
    assert [c for c, _ in tagged] == plain, "tagged generator differs from certify.formula"
    m = len(plain)
    steps = []
    with open(os.path.join(OUT, f"{name}.lrat")) as f:
        for line in f:
            toks = [int(t) for t in line.split()]
            z = toks.index(0, 1)
            steps.append((toks[0], toks[1:z], toks[z + 1:-1]))
    used = sorted({h for _, _, hs in steps for h in hs if h <= m})
    cid = {old: new for new, old in enumerate(used, 1)}
    nxt = len(used)
    for sid, _, _ in steps:
        nxt += 1
        cid[sid] = nxt
    nv = max(abs(l) for c in plain for l in c)
    d = os.path.join(ROOT, "probes", "data")
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, f"{name}.cnf"), "w", newline="\n") as f:
        f.write(f"p cnf {nv} {len(used)}\n")
        for i in used:
            f.write(" ".join(map(str, plain[i - 1])) + " 0\n")
    with open(os.path.join(d, f"{name}.lrat"), "w", newline="\n") as f:
        for sid, lits, hs in steps:
            f.write(f"{cid[sid]} {' '.join(map(str, lits))} 0 {' '.join(str(cid[h]) for h in hs)} 0\n")
    with open(os.path.join(d, f"{name}.wit"), "w", newline="\n") as f:
        for i in used:
            f.write(" ".join(map(str, tagged[i - 1][1])) + "\n")
    kinds = {}
    for i in used:
        kinds[tagged[i - 1][1][0]] = kinds.get(tagged[i - 1][1][0], 0) + 1
    print(name, "core clauses", len(used), "steps", len(steps), "witness kinds", kinds)


if __name__ == "__main__":
    for nm in sys.argv[1:]:
        export(nm)
