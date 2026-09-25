"""Small forward DRUP checker (RUP only), independent of the SAT solvers.

Every added lemma must follow by unit propagation (RUP) from the original clauses plus the lemmas
already checked, and the proof must end with the empty clause or a top-level conflict.  Deletion
lines are ignored.  That is sound, because every clause kept is implied by the formula; it only
makes each check slower.

check(clauses, proof_lines) -> (ok, message)
"""


def check(clauses, proof_lines):
    nv = max((abs(l) for c in clauses for l in c), default=0)
    for line in proof_lines:
        for tok in line.split():
            if tok not in ("d", "0"):
                nv = max(nv, abs(int(tok)))
    val = [0] * (nv + 1)
    watch = [[] for _ in range(2 * nv + 2)]
    cls = []
    trail = []

    def wi(lit):
        return 2 * lit if lit > 0 else -2 * lit + 1

    def value(lit):
        v = val[abs(lit)]
        return v if lit > 0 else -v

    def assign(lit):
        val[abs(lit)] = 1 if lit > 0 else -1
        trail.append(lit)

    def propagate(start):
        i = start
        while i < len(trail):
            false_lit = -trail[i]
            i += 1
            ws = watch[wi(false_lit)]
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
                        watch[wi(c[1])].append(ci)
                        ws[j] = ws[-1]
                        ws.pop()
                        break
                else:
                    if value(c[0]) == -1:
                        return True
                    if value(c[0]) == 0:
                        assign(c[0])
                    j += 1
        return False

    def undo(to):
        while len(trail) > to:
            val[abs(trail.pop())] = 0

    def add_top(c):
        """Add a clause while only top-level assignments exist.  Returns True on conflict."""
        c = list(dict.fromkeys(c))
        if any(value(l) == 1 for l in c):
            c.sort(key=lambda l: -value(l))
        else:
            c.sort(key=lambda l: 0 if value(l) == 0 else 1)
        free = [l for l in c if value(l) != -1]
        if not free:
            return True
        if len(c) == 1 or (len(free) == 1 and value(free[0]) == 0):
            if value(free[0]) == 0:
                pos = len(trail)
                assign(free[0])
                if len(c) >= 2:
                    idx = len(cls); cls.append(c)
                    watch[wi(c[0])].append(idx); watch[wi(c[1])].append(idx)
                return propagate(pos)
            return False
        idx = len(cls)
        cls.append(c)
        watch[wi(c[0])].append(idx)
        watch[wi(c[1])].append(idx)
        return False

    # load the formula: non-unit clauses watched on their first two literals, then units
    units = []
    for c in clauses:
        c = list(dict.fromkeys(c))
        if not c:
            return True, "formula contains the empty clause"
        if len(c) == 1:
            units.append(c[0])
        else:
            idx = len(cls)
            cls.append(c)
            watch[wi(c[0])].append(idx)
            watch[wi(c[1])].append(idx)
    for u in units:
        if value(u) == -1:
            return True, "conflicting unit clauses"
        if value(u) == 0:
            pos = len(trail)
            assign(u)
            if propagate(pos):
                return True, "top-level conflict before the proof"
    checked = 0
    for line in proof_lines:
        toks = line.split()
        if not toks or toks[0] == "d":
            continue
        lits = [int(t) for t in toks if t != "0"]
        base = len(trail)
        conflict = False
        for l in lits:
            v = value(l)
            if v == 1:
                conflict = True
                break
            if v == 0:
                assign(-l)
        if not conflict:
            conflict = propagate(base)
        undo(base)
        if not conflict:
            return False, f"lemma {checked + 1} is not RUP"
        checked += 1
        if not lits:
            return True, f"empty clause derived after {checked} lemmas"
        if add_top(lits):
            return True, f"top-level conflict after {checked} lemmas"
    return False, f"proof ended after {checked} lemmas without deriving the empty clause"
