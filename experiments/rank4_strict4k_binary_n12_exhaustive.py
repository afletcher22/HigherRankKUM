#!/usr/bin/env python3
"""Exact binary strict rank-4 n=12 prescribed-element lifting audit.

Every loopless binary rank-4 matroid on 12 labelled elements can be represented
by multiplicities on the 15 nonzero points of PG(3,2). Strict uniform density
forces projective multiplicity at most two, so this script exhausts the entire
binary strict n=12 class by enumerating c in {0,1,2}^15 with sum 12.

For n=12, rank 4, strict density is exactly:
  m1 <= 2, m2 <= 5, m3 <= 8,
where mj is the maximum cardinality of a rank-j subset.

The script quotients the strict family by GL(4,2), checks every labelled
omitted element on every orbit representative, searches for a CBO of M\e
admitting reinsertion of e, and directly verifies the resulting cyclic order.

Exact finite computation; not Lean certification.
"""

from __future__ import annotations

import itertools
import json
from collections import Counter
from functools import lru_cache

POINTS = tuple(range(1, 16))
N = 12


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
    return (
        max(config),
        max(sum(mult[x] for x in line) for line in LINES),
        max(sum(mult[x] for x in hyp) for hyp in HYPERPLANES),
    )


def strict(config):
    m1, m2, m3 = profile(config)
    return m1 <= 2 and m2 <= 5 and m3 <= 8


def two_deletion_robust(config):
    # s_j >= 2j at n=12, r=4.
    m1, m2, m3 = profile(config)
    return m1 <= 2 and m2 <= 5 and m3 <= 7


def all_configs():
    for d in range(N // 2 + 1):
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


def encode(config):
    value = 0
    for i, m in enumerate(config):
        value |= m << (2 * i)
    return value


def decode(value):
    return tuple((value >> (2 * i)) & 3 for i in range(15))


def transform_encoded(value, perm):
    config = decode(value)
    out = 0
    for i, multiplicity in enumerate(config):
        if multiplicity:
            out |= multiplicity << (2 * (perm[i] - 1))
    return out


def orbit_representatives(strict_configs):
    universe = {encode(c) for c in strict_configs}
    unseen = set(universe)
    perms = gl42_permutations()
    reps = []
    while unseen:
        rep = min(unseen)
        orbit = {transform_encoded(rep, p) for p in perms} & universe
        reps.append((decode(rep), len(orbit)))
        unseen.difference_update(orbit)
    assert sum(size for _, size in reps) == len(strict_configs)
    return reps


def config_values(config):
    values = []
    for point, multiplicity in enumerate(config, start=1):
        values.extend([point] * multiplicity)
    assert len(values) == N
    return tuple(values)


def cyclic_cbo(order, values):
    m = len(order)
    return all(
        rank2(values[order[(i + j) % m]] for j in range(4)) == 4
        for i in range(m)
    )


def find_favorable(values, omitted):
    labels = tuple(i for i in range(N) if i != omitted)
    m = len(labels)
    path = [labels[0]]
    remaining = tuple(labels[1:])

    @lru_cache(None)
    def basis4(labels4):
        return rank2(values[i] for i in labels4) == 4

    def dfs(rem):
        if not rem:
            order = tuple(path)
            for start in range(m - 3, m):
                if not basis4(tuple(order[(start + j) % m] for j in range(4))):
                    return None
            assert cyclic_cbo(order, values)
            for gap in range(m):
                full = list(order)
                full.insert(gap, omitted)
                if cyclic_cbo(tuple(full), values):
                    return (order, gap)
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
    strict_configs = []
    strict_profiles = Counter()
    duplicate_counts = Counter()
    two_delete_count = 0

    for config in all_configs():
        total += 1
        if strict(config):
            strict_configs.append(config)
            strict_profiles[profile(config)] += 1
            duplicate_counts[sum(m == 2 for m in config)] += 1
            if two_deletion_robust(config):
                two_delete_count += 1

    assert total == 1161615
    assert len(strict_configs) == 610295
    assert strict_profiles == Counter({
        (1, 3, 6): 35,
        (1, 3, 7): 420,
        (2, 4, 7): 47460,
        (2, 4, 8): 69300,
        (2, 5, 8): 493080,
    })
    assert two_delete_count == 47915

    reps = orbit_representatives(strict_configs)
    assert len(reps) == 85

    failures = []
    pointed_checks = 0
    for orbit_index, (config, orbit_size) in enumerate(reps):
        values = config_values(config)
        for omitted in range(N):
            pointed_checks += 1
            if find_favorable(values, omitted) is None:
                failures.append({
                    "orbit_index": orbit_index,
                    "orbit_size": orbit_size,
                    "config": list(config),
                    "omitted_label": omitted,
                })

    assert failures == []

    out = {
        "scope": "all binary strict rank-4 matroids on 12 labelled elements",
        "all_multiplicity_vectors_sum_12": total,
        "strict_configs": len(strict_configs),
        "strict_profile_counts": {
            str(k): v for k, v in sorted(strict_profiles.items())
        },
        "strict_duplicate_class_counts": {
            str(k): v for k, v in sorted(duplicate_counts.items())
        },
        "two_deletion_robust_strict_configs": two_delete_count,
        "not_two_deletion_robust_strict_configs": len(strict_configs) - two_delete_count,
        "gl42_orbits": len(reps),
        "gl42_orbit_size_distribution": {
            str(k): v for k, v in sorted(Counter(size for _, size in reps).items())
        },
        "pointed_checks_on_orbit_representatives": pointed_checks,
        "prescribed_element_failure_orbits": 0,
        "existential_failure_orbits": 0,
        "interpretation": (
            "Every prescribed element is favorable throughout the complete "
            "binary strict n=12 class. Most strict configurations are not "
            "two-deletion robust, so this is evidence for the strict 4k branch "
            "beyond the stronger t=0 hypothesis."
        ),
        "claim_level": "exact finite computation; not Lean certification",
    }
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
