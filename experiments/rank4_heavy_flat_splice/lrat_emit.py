"""Convert a DRUP proof into a trimmed LRAT proof, for Mathlib's kernel-checked `from_lrat`.

Forward RUP checking with reason tracking.  For each lemma, the negation of the lemma is assumed,
unit propagation runs to a conflict, and the conflict is analysed back through the reason clauses
of the propagated literals.  Those clauses, in trail order and ending with the conflicting clause,
are the lemma's LRAT hints.  Top-level literals are included through their own reason clauses, so
each hint list is self-contained, as LRAT requires.  Lemmas the final refutation does not use are
dropped.  Deletions in the DRUP proof are ignored (sound; only slower), and no deletion lines are
emitted.

Clause ids: the formula's clauses are 1..m in the order of certs/NAME.cnf; lemmas are numbered
m+1, m+2, ... in proof order.

Usage: python lrat_emit.py NAME   (reads certs/NAME.cnf and certs/NAME.drat.bin,
                                   writes certs/NAME.lrat, appends a line to certs/lrat.jsonl)
"""
import json, os, sys, time
from cert_measure import binary_drat, OUT


def read_dimacs(path):
    cls = []
    with open(path) as f:
        for line in f:
            if line.startswith(("p", "c")):
                continue
            lits = [int(t) for t in line.split()]
            assert lits and lits[-1] == 0
            cls.append(lits[:-1])
    return cls


class Checker:
    def __init__(self, nv):
        self.val = [0] * (nv + 1)
        self.reason = [0] * (nv + 1)
        self.pos = [0] * (nv + 1)
        self.watch = [[] for _ in range(2 * nv + 2)]
        self.cls = [None]            # 1-based clause ids
        self.trail = []

    @staticmethod
    def wi(lit):
        return 2 * lit if lit > 0 else -2 * lit + 1

    def value(self, lit):
        v = self.val[abs(lit)]
        return v if lit > 0 else -v

    def assign(self, lit, why):
        v = abs(lit)
        self.val[v] = 1 if lit > 0 else -1
        self.reason[v] = why
        self.pos[v] = len(self.trail)
        self.trail.append(lit)

    def undo(self, to):
        while len(self.trail) > to:
            self.val[abs(self.trail.pop())] = 0

    def propagate(self, start):
        """Returns the id of a falsified clause, or 0."""
        trail, cls, watch, value = self.trail, self.cls, self.watch, self.value
        i = start
        while i < len(trail):
            false_lit = -trail[i]
            i += 1
            ws = watch[self.wi(false_lit)]
            j = 0
            while j < len(ws):
                ci = ws[j]
                c = cls[ci]
                if c[0] == false_lit:
                    c[0], c[1] = c[1], c[0]
                if value(c[0]) == 1:
                    j += 1
                    continue
                for k in range(2, len(c)):
                    if value(c[k]) != -1:
                        c[1], c[k] = c[k], c[1]
                        watch[self.wi(c[1])].append(ci)
                        ws[j] = ws[-1]
                        ws.pop()
                        break
                else:
                    if value(c[0]) == -1:
                        return ci
                    if value(c[0]) == 0:
                        self.assign(c[0], ci)
                    j += 1
        return 0

    def add(self, lits):
        """Add a clause at top level.  Returns (clause id, id of a falsified clause or 0)."""
        c = list(dict.fromkeys(lits))
        cid = len(self.cls)
        self.cls.append(c)
        if not c:
            return cid, cid
        c.sort(key=lambda l: {1: 0, 0: 1, -1: 2}[self.value(l)])
        if self.value(c[0]) == -1:
            return cid, cid
        if len(c) == 1 or self.value(c[1]) == -1:
            if self.value(c[0]) == 0:
                start = len(self.trail)
                self.assign(c[0], cid)
                if len(c) >= 2:
                    self.watch[self.wi(c[0])].append(cid)
                    self.watch[self.wi(c[1])].append(cid)
                return cid, self.propagate(start)
            if len(c) >= 2:
                self.watch[self.wi(c[0])].append(cid)
                self.watch[self.wi(c[1])].append(cid)
            return cid, 0
        self.watch[self.wi(c[0])].append(cid)
        self.watch[self.wi(c[1])].append(cid)
        return cid, 0

    def hints(self, conflict, assumed):
        """Reason clauses needed to falsify `conflict`, in trail order, then `conflict`."""
        seen = set(assumed)
        stack = []
        for l in self.cls[conflict]:
            v = abs(l)
            if v not in seen:
                seen.add(v)
                stack.append(v)
        used = []
        while stack:
            v = stack.pop()
            r = self.reason[v]
            if r == 0 or r == conflict:
                continue
            used.append((self.pos[v], r))
            for l in self.cls[r]:
                u = abs(l)
                if u not in seen:
                    seen.add(u)
                    stack.append(u)
        used.sort()
        return [r for _, r in used] + [conflict]


def emit(name):
    t0 = time.time()
    formula = read_dimacs(os.path.join(OUT, f"{name}.cnf"))
    proof_path = os.path.join(OUT, f"{name}.drat.bin")
    nv = max(abs(l) for c in formula for l in c)
    for _, lits in binary_drat(proof_path):
        if lits:
            nv = max(nv, max(abs(l) for l in lits))
    ck = Checker(nv)
    m = len(formula)
    steps = {}                       # lemma id -> (lits, hints)
    final = None

    def finish(conflict, assumed=()):
        return ck.hints(conflict, assumed)

    for c in formula:
        _, confl = ck.add(c)
        if confl and final is None:
            final = (len(ck.cls), [], finish(confl))
    if final is None:
        for is_del, lits in binary_drat(proof_path):
            if is_del:
                continue
            base = len(ck.trail)
            assumed = {abs(l) for l in lits}
            confl = 0
            for l in lits:
                v = ck.value(l)
                if v == 1:
                    confl = ck.reason[abs(l)]
                    break
                if v == 0:
                    ck.assign(-l, 0)
            if not confl:
                confl = ck.propagate(base)
            if not confl:
                raise ValueError(f"lemma {len(ck.cls)} is not RUP")
            h = ck.hints(confl, assumed)
            ck.undo(base)
            cid, top = ck.add(lits)
            steps[cid] = (lits, h)
            if not lits:
                final = (cid, [], h)
                break
            if top:
                final = (len(ck.cls), [], finish(top))
                break
    if final is None:
        raise ValueError("proof ended without a refutation")
    fid, _, fh = final
    need, stack = set(), list(fh)
    while stack:
        i = stack.pop()
        if i > m and i not in need and i in steps:
            need.add(i)
            stack.extend(steps[i][1])
    out = os.path.join(OUT, f"{name}.lrat")
    hint_total = 0
    with open(out, "w") as f:
        for i in sorted(need):
            lits, h = steps[i]
            hint_total += len(h)
            f.write(f"{i} {' '.join(map(str, lits))} 0 {' '.join(map(str, h))} 0\n")
        hint_total += len(fh)
        f.write(f"{fid} 0 {' '.join(map(str, fh))} 0\n")
    rec = {"name": name, "formula_clauses": m, "drup_lemmas": len(steps), "lrat_lemmas": len(need) + 1,
           "lrat_hints": hint_total, "lrat_bytes": os.path.getsize(out), "seconds": round(time.time() - t0, 1)}
    print(json.dumps(rec), flush=True)
    with open(os.path.join(OUT, "lrat.jsonl"), "a") as f:
        f.write(json.dumps(rec) + "\n")


if __name__ == "__main__":
    for nm in sys.argv[1:]:
        emit(nm)
