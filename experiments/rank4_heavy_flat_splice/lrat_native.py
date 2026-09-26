"""LRAT proofs written by CaDiCaL itself (option lrat=1), trimmed to the steps the empty clause needs.

This replaces lrat_emit.py (forward RUP with reason tracking, in Python), which takes hours on the
larger formulas.  CaDiCaL writes the hint chains; trimming is one backward pass from the empty
clause.  The result is restricted to the used input clauses and renumbered (core clauses 1..k in
input order, then the steps), then checked with the strict checker lrat_check.py.

Output: certs/NAME_ncore.cnf, certs/NAME_ncore.lrat, certs/NAME_ncore.idx (the 1-based input
indices of the core clauses), and a JSON line on stdout.

Usage: python lrat_native.py NAME...   (reads certs/NAME.cnf)
"""
import json, os, sys, time
import pysat.solvers as PS
from certify import _flush_c_streams
from cert_measure import OUT
from lrat_emit import read_dimacs
from lrat_check import check as lrat_check


def solve_lrat(cls, path):
    s = PS.Cadical195()
    s.configure({"lrat": 1, "binary": 0})
    with open(path, "w+b") as f:
        PS.pysolvers.cadical195_tracepr(s.cadical, f)
        for c in cls:
            s.add_clause(c)
        res = s.solve()
        _flush_c_streams()
        s.delete()
        _flush_c_streams()
    assert res is False, "formula is satisfiable"


def trim(m, path):
    """Steps needed for the empty clause, in proof order, and the used input clauses (1-based).

    Through the API, CaDiCaL numbers clauses with one running counter: input clauses in the order
    they are added, interleaved with steps derived while adding (e.g. an input clause shortened by
    an earlier unit).  Every id is either a printed step or an input clause, so the input ids are
    the ids not used by steps, in order."""
    steps = {}
    order = []
    empty = None
    with open(path) as f:
        for line in f:
            toks = line.split()
            if not toks or toks[1] == "d":
                continue
            t = list(map(int, toks))
            z = t.index(0, 1)
            sid, lits, hints = t[0], t[1:z], t[z + 1:-1]
            steps[sid] = (lits, hints)
            order.append(sid)
            if not lits:
                empty = sid
                break
    assert empty is not None, "no empty clause in the proof"
    orig, i, k = {}, 0, 1
    while i < m:
        if k not in steps:
            i += 1
            orig[k] = i
        k += 1
    need, stack = {empty}, [empty]
    used = set()
    while stack:
        for h in steps[stack.pop()][1]:
            if h in orig:
                used.add(orig[h])
            elif h not in need:
                need.add(h)
                stack.append(h)
    return [s for s in order if s in need], steps, sorted(used), orig


def run(name):
    t0 = time.time()
    cls = read_dimacs(os.path.join(OUT, f"{name}.cnf"))
    nv = max(abs(l) for c in cls for l in c)
    raw = os.path.join(OUT, f"{name}.native.lrat")
    solve_lrat(cls, raw)
    t1 = time.time()
    m = len(cls)
    keep, steps, used, orig = trim(m, raw)
    newidx = {old: new for new, old in enumerate(used, 1)}
    cid = {}
    nxt = len(used)
    for sid in keep:
        nxt += 1
        cid[sid] = nxt
    ref = lambda h: newidx[orig[h]] if h in orig else cid[h]
    lines = [f"{cid[s]} {' '.join(map(str, steps[s][0]))} 0 {' '.join(str(ref(h)) for h in steps[s][1])} 0"
             for s in keep]
    core = [cls[i - 1] for i in used]
    tag = f"{name}_ncore"
    with open(os.path.join(OUT, f"{tag}.cnf"), "w", newline="\n") as f:
        f.write(f"p cnf {nv} {len(core)}\n")
        for c in core:
            f.write(" ".join(map(str, c)) + " 0\n")
    with open(os.path.join(OUT, f"{tag}.lrat"), "w", newline="\n") as f:
        f.write("\n".join(lines) + "\n")
    with open(os.path.join(OUT, f"{tag}.idx"), "w", newline="\n") as f:
        f.write("\n".join(map(str, used)) + "\n")
    t2 = time.time()
    ok, msg = lrat_check(core, lines)
    rec = {"name": name, "clauses": m, "core": len(core), "steps": len(keep),
           "hints": sum(len(steps[s][1]) for s in keep),
           "check": ("VERIFIED " if ok else "REJECTED ") + msg,
           "solve_s": round(t1 - t0), "trim_s": round(t2 - t1), "check_s": round(time.time() - t2)}
    print(json.dumps(rec), flush=True)
    os.remove(raw)
    return rec


if __name__ == "__main__":
    for nm in sys.argv[1:]:
        run(nm)
