#!/usr/bin/env python3
"""Exact binary n=10 audit for the t=0 two-deletion-robust lifting target.

Family:
  rank-four binary represented matroids on 10 labelled elements, where each
  projective point of PG(3,2) has multiplicity at most two.

For n=10, rank 4, universal two-element deletion robustness is equivalent
(on this represented family) to the exact occupancy bounds
  m1 <= 2, m2 <= 4, m3 <= 6.
These imply strict uniform density and t=0 (no 7-point rank-three flat).

The program:
  1. enumerates all 531,531 multiplicity vectors c in {0,1,2}^15 with sum 10;
  2. filters the exact two-deletion-robust family;
  3. quotients it by GL(4,2);
  4. on every orbit representative, checks every labelled omitted element e;
  5. searches for a CBO of M\e into which e can be inserted, and verifies
     the resulting 10-cycle directly by all cyclic four-window rank tests.

Parallel copies remain separately labelled during the CBO search.

This is exact finite computation, not Lean certification.
"""

from __future__ import annotations

import itertools
import json
from collections import Counter
from functools import lru_cache

POINTS = tuple(range(1, 16))
N = 10


def rank2(values):
    pivots = [0] * 4
    r = 0
    for value in values:
        x = value
        while x:
            p = x.bit_length() - 1
            if pivots[p]:
                x ^= pivots[p]
            else:
                pivots[p] = x
                r += 1
                break
    return r


LINES = tuple({
    frozenset((a, b, a ^ b))
    for a, b in itertools.combinations(POINTS, 2)
})

HYPERPLANES = tuple(
    frozenset(
        x for x in POINTS
        if ((normal & x).bit_count() % 2) == 0
    )
    for normal in POINTS
)


def profile(config):
    mult = (0,) + tuple(config)
    m1 = max(config)
    m2 = max(sum(mult[x] for x in line) for line in LINES)
    m3 = max(sum(mult[x] for x in hyp) for hyp in HYPERPLANES)
    return (m1, m2, m3)


def two_deletion_robust(config):
    m1, m2, m3 = profile(config)
    return m1 <= 2 and m2 <= 4 and m3 <= 6


def all_configs():
    # d projective points are doubled; s=10-2d are single.
    for d in range(6):
        s = N - 2 * d
        if s < 0 or d + s > 15:
            continue
        for doubled in itertools.combinations(POINTS, d):
            doubled = set(doubled)
            remaining = [x for x in POINTS if x not in doubled]
            for singles in itertools.combinations(remaining, s):
                c = [0] * 15
                for x in doubled:
                    c[x - 1] = 2
                for x in singles:
                    c[x - 1] = 1
                yield tuple(c)


def gl42_permutations():
    out = []
    for cols in itertools.permutations(POINTS, 4):
        if rank2(cols) != 4:
            continue
        mapping = []
        for x in POINTS:
            y = 0
            for bit in range(4):
                if (x >> bit) & 1:
                    y ^= cols[bit]
            mapping.append(y)
        out.append(tuple(mapping))
    assert len(out) == 20160
    return tuple(out)


def transform_config(config, perm):
    out = [0] * 15
    for x, multiplicity in enumerate(config, start=1):
        out[perm[x - 1] - 1] = multiplicity
    return tuple(out)


def orbit_representatives(robust):
    robust_set = set(robust)
    unseen = set(robust)
    perms = gl42_permutations()
    reps = []
    while unseen:
        rep = min(unseen)
        orbit = {transform_config(rep, p) for p in perms}
        orbit &= robust_set
        reps.append((rep, len(orbit)))
        unseen.difference_update(orbit)
    assert sum(size for _, size in reps) == len(robust)
    return reps


def config_to_labelled_values(config):
    values = []
    point_labels = []
    for point, multiplicity in enumerate(config, start=1):
        for _ in range(multiplicity):
            values.append(point)
            point_labels.append(point)
    assert len(values) == N
    return tuple(values), tuple(point_labels)


def cyclic_cbo(order, values):
    m = len(order)
    return all(
        rank2(values[order[(i + j) % m]] for j in range(4)) == 4
        for i in range(m)
    )


def insertion_succeeds(order, omitted, gap, values):
    full = list(order)
    full.insert(gap, omitted)
    return cyclic_cbo(tuple(full), values)


def find_favorable(values, omitted):
    labels = tuple(i for i in range(N) if i != omitted)
    m = len(labels)

    # Rotation gauge: every deletion CBO can be rotated so labels[0] is first.
    path = [labels[0]]
    remaining = tuple(labels[1:])

    @lru_cache(None)
    def basis4(labels4):
        return rank2(values[i] for i in labels4) == 4

    def wrap_ok():
        order = tuple(path)
        return all(
            basis4(tuple(order[(i + j) % m] for j in range(4)))
            for i in range(m - 3, m)
        )

    def dfs(rem):
        if not rem:
            order = tuple(path)
            if not wrap_ok():
                return None
            assert cyclic_cbo(order, values)
            for gap in range(m):
                if insertion_succeeds(order, omitted, gap, values):
                    return {
                        "deletion_order": list(order),
                        "gap": gap,
                    }
            return None

        for x in rem:
            if len(path) >= 3 and not basis4(tuple(path[-3:] + [x])):
                continue
            path.append(x)
            ans = dfs(tuple(y for y in rem if y != x))
            if ans is not None:
                return ans
            path.pop()
        return None

    return dfs(remaining)


def main():
    total = 0
    robust = []
    all_profile_counts = Counter()
    robust_profile_counts = Counter()
    duplicate_class_counts = Counter()

    for config in all_configs():
        total += 1
        p = profile(config)
        all_profile_counts[p] += 1
        if two_deletion_robust(config):
            robust.append(config)
            robust_profile_counts[p] += 1
            duplicate_class_counts[sum(m == 2 for m in config)] += 1

    assert total == 531531
    assert len(robust) == 28476
    assert robust_profile_counts == Counter({
        (1, 3, 6): 2163,
        (2, 4, 6): 26313,
    })

    reps = orbit_representatives(robust)
    assert len(reps) == 16

    failures = []
    pointed_orbit_checks = 0
    for orbit_index, (config, orbit_size) in enumerate(reps):
        values, projective_points = config_to_labelled_values(config)
        for omitted in range(N):
            pointed_orbit_checks += 1
            witness = find_favorable(values, omitted)
            if witness is None:
                failures.append({
                    "orbit_index": orbit_index,
                    "orbit_size": orbit_size,
                    "config": list(config),
                    "omitted_label": omitted,
                    "omitted_projective_point": projective_points[omitted],
                })

    assert failures == []

    out = {
        "scope": (
            "all binary n=10 multiplicity<=2 representations on PG(3,2) "
            "satisfying universal two-deletion robustness"
        ),
        "all_multiplicity_vectors_sum_10": total,
        "two_deletion_robust_configs": len(robust),
        "robust_profile_counts": {
            str(k): v for k, v in sorted(robust_profile_counts.items())
        },
        "robust_duplicate_class_counts": {
            str(k): v for k, v in sorted(duplicate_class_counts.items())
        },
        "gl42_orbits": len(reps),
        "gl42_orbit_size_distribution": {
            str(k): v for k, v in sorted(Counter(size for _, size in reps).items())
        },
        "pointed_checks_on_orbit_representatives": pointed_orbit_checks,
        "prescribed_element_failure_orbits": 0,
        "existential_failure_orbits": 0,
        "interpretation": (
            "Every labelled omitted element is favorable on every GL(4,2) "
            "orbit representative. Coordinate isomorphisms and permutations "
            "of parallel copies transport these witnesses to the full exact family."
        ),
        "claim_level": "exact finite computation; not Lean certification",
    }
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
