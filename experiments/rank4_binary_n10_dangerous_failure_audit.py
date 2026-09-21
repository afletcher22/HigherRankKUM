#!/usr/bin/env python3
"""Exact strict binary n=10 audit: insertion failure versus dangerous flats.

Enumerates every rank-4 binary multiplicity pattern on 10 labelled columns
compatible with strict density:
  rank-1 flat <= 2, rank-2 flat <= 4, rank-3 flat <= 7.

After quotienting by GL(4,2), every labelled omitted element of every orbit
representative is classified as:

  * favorable: M\e has a CBO and some deletion CBO accepts e;
  * unavailable: M\e has no CBO;
  * eligible insertion failure: M\e has CBOs, but none accepts e.

The point of the audit is to test whether genuine eligible insertion failure
can occur without a dangerous rank-3 flat of size 7.

Finite computation only; not Lean certification.
"""

from collections import Counter
from itertools import combinations, permutations
import json

POINTS = tuple(range(1, 16))


def rank2(vals):
    piv = [0] * 4
    r = 0
    for value in vals:
        x = value
        while x:
            i = x.bit_length() - 1
            if piv[i]:
                x ^= piv[i]
            else:
                piv[i] = x
                r += 1
                break
    return r


def dot(a, b):
    return (a & b).bit_count() & 1


LINES = sorted({
    frozenset(x for x in POINTS if rank2((a, b, x)) <= 2)
    for a, b in combinations(POINTS, 2)
}, key=lambda s: tuple(sorted(s)))

HYPERS = tuple(
    frozenset(x for x in POINTS if dot(n, x) == 0)
    for n in POINTS
)


def profile(c):
    def occ(F):
        return sum(c[x - 1] for x in F)
    return max(c), max(map(occ, LINES)), max(map(occ, HYPERS))


def strict_patterns():
    out = set()
    for d in range(6):
        singles = 10 - 2 * d
        support_size = d + singles
        if singles < 0 or support_size > 15:
            continue
        for support in combinations(range(15), support_size):
            for doubled in combinations(support, d):
                c = [0] * 15
                for i in support:
                    c[i] = 1
                for i in doubled:
                    c[i] = 2
                c = tuple(c)
                m1, m2, m3 = profile(c)
                if m1 <= 2 and m2 <= 4 and m3 <= 7:
                    out.add(c)
    return out


def gl_perms():
    out = []
    for imgs in permutations(POINTS, 4):
        if rank2(imgs) != 4:
            continue
        perm = []
        for x in POINTS:
            y = 0
            for j, bit in enumerate((1, 2, 4, 8)):
                if x & bit:
                    y ^= imgs[j]
            perm.append(y - 1)
        out.append(tuple(perm))
    assert len(out) == 20160
    return out


def apply_perm(c, g):
    out = [0] * 15
    for i, v in enumerate(c):
        out[g[i]] = v
    return tuple(out)


def orbit_reps(patterns):
    G = gl_perms()
    unseen = set(patterns)
    out = []
    while unseen:
        c = min(unseen)
        orb = {apply_perm(c, g) for g in G} & patterns
        unseen -= orb
        out.append((c, len(orb)))
    return out


def columns(c):
    out = []
    for i, v in enumerate(c):
        out.extend([i + 1] * v)
    assert len(out) == 10
    return tuple(out)


def cbo(order, cols):
    m = len(order)
    return all(
        rank2(tuple(cols[order[(i + j) % m]] for j in range(4))) == 4
        for i in range(m)
    )


def deletion_cbos(cols, e):
    labels = [i for i in range(10) if i != e]
    first = min(labels)
    path = [first]
    out = []

    def rec(rem):
        if not rem:
            order = tuple(path)
            if cbo(order, cols):
                out.append(order)
            return
        for x in rem:
            if len(path) >= 3:
                if rank2(tuple(cols[i] for i in path[-3:] + [x])) != 4:
                    continue
            path.append(x)
            rec([y for y in rem if y != x])
            path.pop()

    rec([x for x in labels if x != first])
    return out


def insertable(cols, e, order):
    for gap in range(len(order)):
        full = list(order)
        full.insert(gap, e)
        if cbo(tuple(full), cols):
            return True
    return False


def dangerous_hypers(c):
    return [H for H in HYPERS if sum(c[x - 1] for x in H) == 7]


def main():
    pats = strict_patterns()
    assert len(pats) == 191436
    reps = orbit_reps(pats)
    assert len(reps) == 37
    assert sum(size for _, size in reps) == len(pats)

    prof_hist = Counter()
    matroid_orbits_with_danger = 0
    favorable = 0
    unavailable = 0
    true_failures = []
    orbit_rows = []

    for oi, (c, osize) in enumerate(reps):
        prof = profile(c)
        prof_hist[prof] += 1
        Hs = dangerous_hypers(c)
        if Hs:
            matroid_orbits_with_danger += 1

        cols = columns(c)
        row = {
            "orbit_index": oi,
            "orbit_size": osize,
            "profile": list(prof),
            "dangerous_hyperplanes": len(Hs),
            "unavailable_labels": [],
            "eligible_insertion_failure_labels": [],
        }

        for e in range(10):
            orders = deletion_cbos(cols, e)
            if not orders:
                unavailable += 1
                row["unavailable_labels"].append(e)
                continue
            if any(insertable(cols, e, o) for o in orders):
                favorable += 1
                continue

            row["eligible_insertion_failure_labels"].append(e)
            point = cols[e]
            containing = sum(point in H for H in Hs)
            true_failures.append({
                "orbit_index": oi,
                "label": e,
                "deletion_cbos": len(orders),
                "profile": list(prof),
                "dangerous_hyperplanes": len(Hs),
                "dangerous_hyperplanes_containing_e": containing,
                "e_lies_in_every_dangerous_hyperplane": containing == len(Hs),
            })

        orbit_rows.append(row)

    assert favorable + unavailable + len(true_failures) == 37 * 10
    assert len(true_failures) == 3
    assert all(x["profile"][2] == 7 for x in true_failures)
    assert all(x["e_lies_in_every_dangerous_hyperplane"] for x in true_failures)

    print(json.dumps({
        "scope": "exact strict binary rank-4 n=10 multiplicity census",
        "strict_multiplicity_patterns": len(pats),
        "gl4_2_orbits": len(reps),
        "orbit_profile_histogram": {
            str(k): v for k, v in sorted(prof_hist.items())
        },
        "orbits_with_dangerous_rank3_flat": matroid_orbits_with_danger,
        "pointed_orbit_representatives": 370,
        "favorable_pointed_cases": favorable,
        "deletions_with_no_cbo": unavailable,
        "eligible_insertion_failures": len(true_failures),
        "eligible_failure_records": true_failures,
        "interpretation": (
            "Every genuine eligible prescribed-element insertion failure in "
            "the complete strict binary n=10 class occurs in a matroid with "
            "a dangerous 7-element rank-3 flat. No t=0 orbit has such a failure."
        ),
        "claim_level": "exact finite computation; not Lean certification",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
