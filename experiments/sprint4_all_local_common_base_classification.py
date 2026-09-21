#!/usr/bin/env python3
"""Exact classification of all four-element rank-two common-base pairs.

Enumerate all rank-two matroids on the labelled ground {0,1,2,3}.  For every
ordered pair (L,S) having CURRENT={0,1} as a common base, classify the common
bases without imposing the earlier closure-free surrogate.

The key guardrail is stronger than the original Sprint 4 certificate:

* if there is an alternative common base but no cross common base, then the
  only alternative is OPPOSITE={2,3};
* exactly two ordered pairs have this behavior;
* they are the two complementary crossing-perfect-matching base patterns.

Thus any local boundary with an alternative common base but no cross repair is
one of a tiny exceptional family.  This is an exact abstract finite result,
not yet the global odd-cycle theorem needed for rank-four KUM.
"""

import json
from collections import Counter
from itertools import combinations

GROUND = tuple(range(4))
PAIRS = tuple(combinations(GROUND, 2))
CURRENT = (0, 1)
OPPOSITE = (2, 3)
CROSS = {(0, 2), (0, 3), (1, 2), (1, 3)}


def canon_pair(values):
    return tuple(sorted(values))


def satisfies_basis_exchange(bases):
    bases = set(bases)
    if not bases:
        return False
    for left in bases:
        for right in bases:
            for e in set(left) - set(right):
                if not any(
                    canon_pair((set(left) - {e}) | {f}) in bases
                    for f in set(right) - set(left)
                ):
                    return False
    return True


def rank_two_matroids():
    out = []
    for mask in range(1, 1 << len(PAIRS)):
        bases = tuple(
            PAIRS[i] for i in range(len(PAIRS)) if (mask >> i) & 1
        )
        if satisfies_basis_exchange(bases):
            out.append(bases)
    return tuple(out)


def as_json_bases(bases):
    return [list(base) for base in bases]


def main():
    matroids = rank_two_matroids()
    common_count_histogram = Counter()
    with_current = 0
    unique_current = 0
    with_alternative = 0
    with_cross = 0
    no_cross = 0
    alternative_without_cross = []

    for left in matroids:
        for dual_right in matroids:
            if CURRENT not in left or CURRENT not in dual_right:
                continue

            with_current += 1
            common = tuple(sorted(set(left) & set(dual_right)))
            common_count_histogram[len(common)] += 1
            alternatives = tuple(base for base in common if base != CURRENT)
            cross = tuple(base for base in common if base in CROSS)

            if alternatives:
                with_alternative += 1
            else:
                unique_current += 1

            if cross:
                with_cross += 1
            else:
                no_cross += 1
                if alternatives:
                    alternative_without_cross.append(
                        {
                            "left_bases": as_json_bases(left),
                            "dual_right_bases": as_json_bases(dual_right),
                            "common_bases": as_json_bases(common),
                            "alternative_bases": as_json_bases(alternatives),
                        }
                    )

    assert len(matroids) == 36
    assert with_current == 289
    assert common_count_histogram == Counter({1: 81, 2: 110, 3: 48, 4: 34, 5: 15, 6: 1})
    assert unique_current == 81
    assert with_alternative == 208
    assert with_cross == 206
    assert no_cross == 83
    assert len(alternative_without_cross) == 2
    assert all(
        item["alternative_bases"] == [list(OPPOSITE)]
        for item in alternative_without_cross
    )

    expected_patterns = {
        (
            ((0, 1), (0, 3), (1, 2), (2, 3)),
            ((0, 1), (0, 2), (1, 3), (2, 3)),
        ),
        (
            ((0, 1), (0, 2), (1, 3), (2, 3)),
            ((0, 1), (0, 3), (1, 2), (2, 3)),
        ),
    }
    actual_patterns = {
        (
            tuple(tuple(base) for base in item["left_bases"]),
            tuple(tuple(base) for base in item["dual_right_bases"]),
        )
        for item in alternative_without_cross
    }
    assert actual_patterns == expected_patterns

    out = {
        "scope": "all ordered pairs of rank-two matroids on a fixed four-element ground with the current pair a common base",
        "ground": list(GROUND),
        "current_pair": list(CURRENT),
        "opposite_pair": list(OPPOSITE),
        "rank_two_matroids_examined": len(matroids),
        "ordered_pairs_with_current_common_base": with_current,
        "common_base_count_histogram": {
            str(k): common_count_histogram[k]
            for k in sorted(common_count_histogram)
        },
        "unique_current_common_base": unique_current,
        "with_alternative_common_base": with_alternative,
        "with_cross_common_base": with_cross,
        "without_cross_common_base": no_cross,
        "with_alternative_but_without_cross_common_base": len(alternative_without_cross),
        "alternative_without_cross_examples": alternative_without_cross,
        "status": "exact abstract four-element classification; alternative-without-cross has exactly two complementary matching types",
    }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
