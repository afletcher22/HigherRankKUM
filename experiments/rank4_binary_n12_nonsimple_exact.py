#!/usr/bin/env python3
"""Exact binary n=12 non-simple favorable-lifting census.

Enumerates every multiplicity vector c in {0,1,2}^15 of total size 12 on
PG(3,2).  Universal one-element deletion robustness at rank four is exactly
the flat-cap condition

    rank 1 <= 2, rank 2 <= 5, rank 3 <= 8.

The surviving 610,295 patterns are quotiented by GL(4,2).  For every one of
the 85 orbit representatives and every labelled omitted element, the script
constructs and directly verifies a deletion CBO admitting reinsertion.

Finding a witness is a certificate of favorability; no inference from random
sampling is used.  This is finite computation, not Lean certification.
"""

from itertools import combinations, permutations
from collections import Counter
import json


POINTS = tuple(range(1, 16))


def rank2(values):
    pivots = [0] * 4
    r = 0
    for value in values:
        x = value
        while x:
            i = x.bit_length() - 1
            if pivots[i]:
                x ^= pivots[i]
            else:
                pivots[i] = x
                r += 1
                break
    return r


def dot_bits(a, b):
    return (a & b).bit_count() & 1


LINES = sorted({
    frozenset(x for x in POINTS if rank2((a, b, x)) <= 2)
    for a, b in combinations(POINTS, 2)
}, key=lambda s: tuple(sorted(s)))

HYPERPLANES = tuple(
    frozenset(x for x in POINTS if dot_bits(n, x) == 0)
    for n in POINTS
)


def occupancy_profile(c):
    def occ(flat):
        return sum(c[x - 1] for x in flat)
    return (
        max(c),
        max(map(occ, LINES)),
        max(map(occ, HYPERPLANES)),
    )


def qualifying_patterns():
    out = set()
    by_doubles = Counter()
    for d in range(7):
        singles = 12 - 2 * d
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
                m1, m2, m3 = occupancy_profile(c)
                if m1 <= 2 and m2 <= 5 and m3 <= 8:
                    out.add(c)
                    by_doubles[d] += 1
    return out, by_doubles


def gl_permutations():
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


def orbit_representatives(patterns):
    group = gl_permutations()
    unseen = set(patterns)
    reps = []
    while unseen:
        c = min(unseen)
        orb = {apply_perm(c, g) for g in group} & patterns
        unseen -= orb
        reps.append((c, len(orb)))
    return reps


def columns(c):
    out = []
    for i, v in enumerate(c):
        out.extend([i + 1] * v)
    assert len(out) == 12
    return tuple(out)


def cbo(order, cols):
    m = len(order)
    return all(
        rank2(tuple(cols[order[(i + j) % m]] for j in range(4))) == 4
        for i in range(m)
    )


def favorable_witness(cols, omitted):
    labels = [i for i in range(12) if i != omitted]
    first = min(labels)
    path = [first]

    def insertion_gap(order):
        for gap in range(len(order)):
            full = list(order)
            full.insert(gap, omitted)
            if cbo(tuple(full), cols):
                return gap
        return None

    def rec(rem):
        if not rem:
            order = tuple(path)
            if not cbo(order, cols):
                return None
            gap = insertion_gap(order)
            if gap is None:
                return None
            return order, gap

        for x in rem:
            if len(path) >= 3:
                if rank2(tuple(cols[i] for i in path[-3:] + [x])) != 4:
                    continue
            path.append(x)
            ans = rec([y for y in rem if y != x])
            path.pop()
            if ans is not None:
                return ans
        return None

    return rec([x for x in labels if x != first])


def main():
    patterns, by_doubles = qualifying_patterns()
    assert len(patterns) == 610295

    reps = orbit_representatives(patterns)
    assert len(reps) == 85
    assert sum(size for _, size in reps) == len(patterns)

    orbit_sizes = Counter()
    pointed = 0
    failures = []
    for oi, (c, orbit_size) in enumerate(reps):
        orbit_sizes[orbit_size] += 1
        cols = columns(c)
        for e in range(12):
            pointed += 1
            witness = favorable_witness(cols, e)
            if witness is None:
                failures.append([oi, e])
                continue
            order, gap = witness
            assert cbo(order, cols)
            full = list(order)
            full.insert(gap, e)
            assert cbo(tuple(full), cols)

    assert failures == []

    print(json.dumps({
        "scope": "exact binary rank-4 n=12 one-deletion-robust represented multisets",
        "qualifying_multiplicity_patterns": len(patterns),
        "qualifying_by_number_of_doubled_projective_points":
            dict(sorted(by_doubles.items())),
        "gl4_2_orbits": len(reps),
        "orbit_size_histogram": dict(sorted(orbit_sizes.items())),
        "orbit_representative_pointed_deletions_checked": pointed,
        "prescribed_element_failures": len(failures),
        "interpretation": (
            "Every omitted label has a verified favorable deletion CBO in "
            "every GL(4,2) orbit representative."
        ),
        "claim_level": "exact finite computation; not Lean certification",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
