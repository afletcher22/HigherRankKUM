"""Restrict an LRAT certificate to the formula clauses it actually uses.

Reads certs/NAME.cnf and certs/NAME.lrat and writes certs/NAME_core.cnf and certs/NAME_core.lrat.
The core CNF keeps only the formula clauses referenced by some hint, in their original order, with
variables renumbered densely; clause ids are renumbered to match.  An unsatisfiable subformula
certifies the full claim, and the Lean encoding lemma then only has to justify the core clauses.

With 'keepvars', variables keep their original numbers (needed when a Lean encoding lemma decodes
variable numbers), and the output is certs/NAME_corek.{cnf,lrat}.

Usage: python lrat_core.py [keepvars] NAME...
"""
import json, os, sys
from lrat_emit import read_dimacs
from cert_measure import OUT


def core(name, keepvars=False):
    formula = read_dimacs(os.path.join(OUT, f"{name}.cnf"))
    m = len(formula)
    steps = []
    with open(os.path.join(OUT, f"{name}.lrat")) as f:
        for line in f:
            toks = [int(t) for t in line.split()]
            z = toks.index(0, 1)
            steps.append((toks[0], toks[1:z], toks[z + 1:-1]))
    used = sorted({h for _, _, hs in steps for h in hs if h <= m})
    cid = {old: new for new, old in enumerate(used, 1)}
    vars_ = sorted({abs(l) for i in used for l in formula[i - 1]} |
                   {abs(l) for _, lits, _ in steps for l in lits})
    vid = {v: v for v in vars_} if keepvars else {old: new for new, old in enumerate(vars_, 1)}
    nvars = max(abs(l) for c in formula for l in c) if keepvars else len(vars_)
    suffix = "_corek" if keepvars else "_core"
    ren = lambda l: vid[abs(l)] if l > 0 else -vid[abs(l)]
    nxt = len(used)
    for sid, _, _ in steps:
        nxt += 1
        cid[sid] = nxt
    with open(os.path.join(OUT, f"{name}{suffix}.cnf"), "w") as f:
        f.write(f"p cnf {nvars} {len(used)}\n")
        for i in used:
            f.write(" ".join(str(ren(l)) for l in formula[i - 1]) + " 0\n")
    with open(os.path.join(OUT, f"{name}{suffix}.lrat"), "w") as f:
        for sid, lits, hs in steps:
            f.write(f"{cid[sid]} {' '.join(str(ren(l)) for l in lits)} 0 "
                    f"{' '.join(str(cid[h]) for h in hs)} 0\n")
    rec = {"name": name, "formula_clauses": m, "core_clauses": len(used),
           "core_literals": sum(len(formula[i - 1]) for i in used), "core_vars": len(vars_),
           "lrat_steps": len(steps), "lrat_hints": sum(len(hs) for _, _, hs in steps),
           "core_cnf_bytes": os.path.getsize(os.path.join(OUT, f"{name}{suffix}.cnf")),
           "core_lrat_bytes": os.path.getsize(os.path.join(OUT, f"{name}{suffix}.lrat"))}
    print(json.dumps(rec), flush=True)
    with open(os.path.join(OUT, "core.jsonl"), "a") as f:
        f.write(json.dumps(rec) + "\n")


if __name__ == "__main__":
    args = sys.argv[1:]
    keep = bool(args) and args[0] == "keepvars"
    for nm in args[1:] if keep else args:
        core(nm, keep)
