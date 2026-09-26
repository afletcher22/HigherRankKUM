"""Certificates for the rank-4 extension theorem with per-clause witnesses for Lean.

Re-emits the extension formulas of local_sat.py (linear, length L) and cyclic_sat.py (cyclic, N)
with the arithmetic variable numbering 4X+v ("r(X) >= v", X a bitmask over the positions) that
the Lean witness layer decodes.  Positions 0..3 are the basis S; positions 4.. are e_0, e_1, ...
Rank axioms are imposed on the subsets of the blocks S + {w consecutive e's} (w = 6), exactly as in
local_sat.py / cyclic_sat.py, and duplicate clauses are dropped keeping the first occurrence.

Then: solve with CaDiCaL (DRUP), convert to trimmed LRAT, restrict to the used clauses, and
write <out>/NAME.{cnf,lrat,wit}.  Witness tokens:

  o X v | c X v | m X a v | i X a v | s X a b v   rank axioms (as in lean_witness.py)
  b X                                             [(X,4)]: S or an original window is a basis
  t q_0 .. q_{n-1}                                interleaving: the merged sequence q; the clause
                                                  lists -(W_j,4) for the windows W_j of q that
                                                  contain a position < 4, in order of j

Usage: python ext_witness.py OUTDIR NAME...   (NAME: lin14, cyc8, cyc10, cyc12)
"""
import itertools, json, os, shutil, sys, time
import pysat.solvers as PS
from certify import _flush_c_streams
from cert_measure import OUT, binary_drat
from lrat_emit import emit
from lrat_check import check as lrat_check


def var(X, v):
    return 4 * X + v


def mask(ps):
    return sum(1 << p for p in ps)


class Formula:
    def __init__(self):
        self.cls, self.tags, self.seen = [], [], set()

    def add(self, c, tag):
        key = tuple(c)
        if key in self.seen:
            return
        self.seen.add(key)
        self.cls.append(list(c))
        self.tags.append(tag)


def rank_axioms(F, blocks):
    pc = lambda X: bin(X).count("1")
    done = set()
    for B in blocks:
        B = sorted(B)
        subsets = [mask(c) for r in range(len(B) + 1) for c in itertools.combinations(B, r)]
        for X in subsets:
            if X in done:
                continue
            done.add(X)
            for v in range(1, 4):
                F.add([-var(X, v + 1), var(X, v)], ("o", X, v))
            for v in range(pc(X) + 1, 5):
                F.add([-var(X, v)], ("c", X, v))
        for X in subsets:
            out = [x for x in B if not X >> x & 1]
            for a in out:
                T = X | 1 << a
                for v in range(1, 5):
                    F.add([-var(X, v), var(T, v)], ("m", X, a, v))
                    if v < 4:
                        F.add([-var(T, v + 1), var(X, v)], ("i", X, a, v))
                for b in out:
                    if b <= a:
                        continue
                    U, Xb = T | 1 << b, X | 1 << b
                    for v in range(1, 5):
                        c = [-var(U, v), var(T, v), var(Xb, v), var(X, v)]
                        if v >= 2:
                            c.append(-var(X, v - 1))
                        F.add(c, ("s", X, a, b, v))


def interleaving_clause(seq, cyclic):
    n = len(seq)
    starts = range(n) if cyclic else range(n - 3)
    lits = []
    for j in starts:
        W = [seq[(j + t) % n] for t in range(4)]
        if any(x < 4 for x in W):
            lits.append(-var(mask(W), 4))
    return lits


def build_linear(L, w=6):
    F = Formula()
    E = [4 + i for i in range(L)]
    rank_axioms(F, [[0, 1, 2, 3] + E[i:i + w] for i in range(L - w + 1)])
    F.add([var(0b1111, 4)], ("b", 0b1111))
    for i in range(L - 3):
        F.add([var(mask(E[i:i + 4]), 4)], ("b", mask(E[i:i + 4])))
    for perm in itertools.permutations(range(4)):
        for gs in itertools.combinations_with_replacement(range(3, L - 2), 4):
            seq, gi = [], 0
            for pos in range(L + 1):
                while gi < 4 and gs[gi] == pos:
                    seq.append(perm[gi]); gi += 1
                if pos < L:
                    seq.append(E[pos])
            F.add(interleaving_clause(seq, False), ("t",) + tuple(seq))
    return F


def build_cyclic(N, w=6):
    F = Formula()
    E = [4 + i for i in range(N)]
    rank_axioms(F, [[0, 1, 2, 3] + [E[(i + j) % N] for j in range(w)] for i in range(N)])
    F.add([var(0b1111, 4)], ("b", 0b1111))
    for i in range(N):
        m = mask(E[(i + t) % N] for t in range(4))
        F.add([var(m, 4)], ("b", m))
    for perm in itertools.permutations(range(4)):
        for gs in itertools.combinations_with_replacement(range(N), 4):
            seq, gi = [], 0
            for pos in range(N):
                while gi < 4 and gs[gi] == pos:
                    seq.append(perm[gi]); gi += 1
                seq.append(E[pos])
            F.add(interleaving_clause(seq, True), ("t",) + tuple(seq))
    return F


def run(outdir, name):
    t0 = time.time()
    F = build_linear(int(name[3:])) if name.startswith("lin") else build_cyclic(int(name[3:]))
    tag = f"x{name}"
    cnf = os.path.join(OUT, f"{tag}.cnf")
    nv = max(abs(l) for c in F.cls for l in c)
    with open(cnf, "w") as f:
        f.write(f"p cnf {nv} {len(F.cls)}\n")
        for c in F.cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    s = PS.Cadical195(bootstrap_with=F.cls, with_proof=True)
    assert not s.solve(), "formula is satisfiable"
    _flush_c_streams()
    s.prfile.seek(0)
    with open(os.path.join(OUT, f"{tag}.drat.bin"), "wb") as f:
        shutil.copyfileobj(s.prfile, f)
    s.delete()
    emit(tag)
    m = len(F.cls)
    steps = []
    with open(os.path.join(OUT, f"{tag}.lrat")) as f:
        for line in f:
            toks = [int(x) for x in line.split()]
            z = toks.index(0, 1)
            steps.append((toks[0], toks[1:z], toks[z + 1:-1]))
    used = sorted({h for _, _, hs in steps for h in hs if h <= m})
    cid = {old: new for new, old in enumerate(used, 1)}
    nxt = len(used)
    for sid, _, _ in steps:
        nxt += 1
        cid[sid] = nxt
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, f"{tag}.cnf"), "w", newline="\n") as f:
        f.write(f"p cnf {nv} {len(used)}\n")
        for i in used:
            f.write(" ".join(map(str, F.cls[i - 1])) + " 0\n")
    lrat_lines = [f"{cid[sid]} {' '.join(map(str, lits))} 0 {' '.join(str(cid[h]) for h in hs)} 0"
                  for sid, lits, hs in steps]
    with open(os.path.join(outdir, f"{tag}.lrat"), "w", newline="\n") as f:
        f.write("\n".join(lrat_lines) + "\n")
    with open(os.path.join(outdir, f"{tag}.wit"), "w", newline="\n") as f:
        for i in used:
            f.write(" ".join(map(str, F.tags[i - 1])) + "\n")
    ok, msg = lrat_check([F.cls[i - 1] for i in used], lrat_lines)
    kinds = {}
    for i in used:
        kinds[F.tags[i - 1][0]] = kinds.get(F.tags[i - 1][0], 0) + 1
    rec = {"name": tag, "clauses": m, "core": len(used), "steps": len(steps),
           "hints": sum(len(hs) for _, _, hs in steps), "kinds": kinds,
           "check": ("VERIFIED " if ok else "REJECTED ") + msg, "seconds": round(time.time() - t0)}
    print(json.dumps(rec), flush=True)


if __name__ == "__main__":
    outdir = sys.argv[1]
    for nm in sys.argv[2:]:
        run(outdir, nm)
