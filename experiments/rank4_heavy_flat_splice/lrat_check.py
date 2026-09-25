"""Strict, independent LRAT checker (RUP steps only, as Mathlib's `from_lrat` accepts).

For every step `id lits 0 hints 0`: assume the negation of `lits`, then process the hints in order.
Every hint but the last must become unit (exactly one unassigned literal, all others false), and
its remaining literal is assigned.  The last hint must be falsified.  A hint that is satisfied, or
has two unassigned literals, is an error.  The proof must end with the empty clause.

Usage: python lrat_check.py NAME   (reads certs/NAME.cnf and certs/NAME.lrat)
"""
import os, sys, time
from lrat_emit import read_dimacs
from cert_measure import OUT


def check(formula, lrat_lines):
    db = {i + 1: c for i, c in enumerate(formula)}
    for n, line in enumerate(lrat_lines, 1):
        toks = [int(t) if t != "d" else "d" for t in line.split()]
        if len(toks) > 1 and toks[1] == "d":
            for i in toks[2:-1]:
                db.pop(i, None)
            continue
        sid = toks[0]
        z = toks.index(0, 1)
        lits, hints = toks[1:z], toks[z + 1:-1]
        assert toks[-1] == 0, f"line {n}: missing terminator"
        if sid in db:
            return False, f"line {n}: clause id {sid} reused"
        val = {}
        for l in lits:
            val[abs(l)] = -1 if l > 0 else 1
        for k, h in enumerate(hints):
            if h not in db:
                return False, f"line {n}: hint {h} does not exist"
            free = []
            for l in db[h]:
                v = val.get(abs(l), 0)
                v = v if l > 0 else -v
                if v == 1:
                    return False, f"line {n}: hint {h} is satisfied"
                if v == 0 and l not in free:
                    free.append(l)
            last = k == len(hints) - 1
            if last:
                if free:
                    return False, f"line {n}: final hint {h} is not falsified"
            else:
                if len(free) != 1:
                    return False, f"line {n}: hint {h} is not unit ({len(free)} free literals)"
                val[abs(free[0])] = 1 if free[0] > 0 else -1
        if not hints:
            return False, f"line {n}: no hints"
        db[sid] = lits
        if not lits:
            return True, f"empty clause at step {sid} after {n} lines"
    return False, "no empty clause"


if __name__ == "__main__":
    for nm in sys.argv[1:]:
        t = time.time()
        formula = read_dimacs(os.path.join(OUT, f"{nm}.cnf"))
        with open(os.path.join(OUT, f"{nm}.lrat")) as f:
            ok, msg = check(formula, f.read().splitlines())
        print(f"{nm}: {'VERIFIED' if ok else 'REJECTED'} ({msg}) {time.time() - t:.1f}s", flush=True)
