#!/usr/bin/env python3
"""Exact abstract four-element guardrail for rank-four local repair.

Enumerate every rank-two matroid on the labelled ground {0,1,2,3} by its
nonempty family of two-element bases satisfying basis exchange.  For each
ordered pair (L,S), regard B={0,1} as the current common base and D={2,3} as
the opposite pair.  Keep precisely the configurations matching the negation
of the local rigidity alternatives:

* neither element of D is a loop of L;
* neither element of B is a coloop of S.

The local rigidity theorem predicts that B cannot then be the unique common
base.  This script checks that prediction abstractly, and also records whether
an alternative can always be chosen as a one-element cross exchange.

It cannot: exactly two ordered boundary pairs have no cross common base; in
those cases the only alternative is the wholesale swap D.  This certificate
therefore guards against strengthening the formal closure-free corollary from
"alternative 2+2 repartition" to "cross exchange" without additional
hypotheses.
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


def is_loop(bases, element):
    return all(element not in base for base in bases)


def is_coloop(bases, element):
    return all(element in base for base in bases)


def as_json_bases(bases):
    return [list(base) for base in bases]


def main():
    matroids = rank_two_matroids()
    histogram = Counter()
    qualifying = 0
    no_alternative = 0
    with_cross = 0
    wholesale_only = []

    for left in matroids:
        for dual_right in matroids:
            if CURRENT not in left or CURRENT not in dual_right:
                continue
            if any(is_loop(left, e) for e in OPPOSITE):
                continue
            if any(is_coloop(dual_right, e) for e in CURRENT):
                continue

            qualifying += 1
            common = tuple(sorted(set(left) & set(dual_right)))
            histogram[len(common)] += 1

            alternatives = tuple(base for base in common if base != CURRENT)
            if not alternatives:
                no_alternative += 1

            cross = tuple(base for base in common if base in CROSS)
            if cross:
                with_cross += 1
            elif alternatives == (OPPOSITE,):
                wholesale_only.append(
                    {
                        "left_bases": as_json_bases(left),
                        "dual_right_bases": as_json_bases(dual_right),
                    }
                )

    assert len(matroids) == 36
    assert qualifying == 100
    assert no_alternative == 0
    assert with_cross == 98
    assert len(wholesale_only) == 2
    assert histogram == Counter({2: 22, 3: 28, 4: 34, 5: 15, 6: 1})

    out = {
        "scope": (
            "all rank-two matroid base families on a fixed four-element ground; "
            "abstract local guardrail"
        ),
        "ground": list(GROUND),
        "current_pair": list(CURRENT),
        "opposite_pair": list(OPPOSITE),
        "rank_two_matroids_examined": len(matroids),
        "ordered_boundary_pairs_checked": len(matroids) ** 2,
        "closure_free_surrogate_pairs_with_current_common_base": qualifying,
        "common_base_count_histogram": {
            str(k): histogram[k] for k in sorted(histogram)
        },
        "closure_free_with_no_alternative_common_base": no_alternative,
        "closure_free_with_cross_common_base": with_cross,
        "closure_free_where_only_alternative_is_wholesale_swap": len(wholesale_only),
        "wholesale_swap_only_examples": wholesale_only,
        "status": (
            "exact finite abstract guardrail; not a matroid-representation or "
            "global KUM theorem"
        ),
    }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
