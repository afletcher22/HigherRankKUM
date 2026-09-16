#!/usr/bin/env python3
"""Exhaustive normalized N=5 binary audit of the Sprint 4 closure potential.

Scope: rank-four pair cycles with five pair blocks represented over GF(2)^4.
Any admissible cycle has B0 union B1 as a basis, so after a linear change of
coordinates we may normalize

    B0 = (1,2), B1 = (4,8).

We then enumerate every choice of the remaining three unordered nonzero-vector
pairs, allowing repeated vector values across different labelled elements,
subject to every adjacent pair-block union being a basis.

For |E|=10 and rank 4, strict uniform density is equivalent to:
  * every rank-one flat has at most 2 labelled elements;
  * every rank-two flat has at most 4 labelled elements;
  * every rank-three flat has at most 7 labelled elements.
Proper rank-four subsets automatically satisfy the strict inequality.

The candidate potential is

  Phi = sum_i (
      |B_{i+1} intersect cl(B_{i-1})| +
      |B_i intersect cl(B_{i+2})|
  ).

The audit asks whether every strict-density unorientable normalized cycle has a
legal full 2+2 repartition that both strictly increases Phi and is orientable.
This is an exact finite represented-matroid result, not a theorem for arbitrary
matroids, arbitrary odd N, or arbitrary fields.
"""

import json
from collections import Counter
from itertools import combinations

VECTORS = tuple(range(1, 16))
PAIRS = tuple(combinations(VECTORS, 2))
B0 = (1, 2)
B1 = (4, 8)
N = 5


def rank(values):
    basis = [0] * 4
    r = 0
    for value in values:
        x = value
        while x:
            pivot = x.bit_length() - 1
            if basis[pivot]:
                x ^= basis[pivot]
            else:
                basis[pivot] = x
                r += 1
                break
    return r


def span(values):
    out = {0}
    for value in values:
        out |= {x ^ value for x in tuple(out)}
    return frozenset(out)


def is_basis(left, right):
    return rank(left + right) == 4


def relation(state, i):
    out = []
    for a in (0, 1):
        row = []
        for b in (0, 1):
            row.append(
                rank((state[i][1 - a],) + state[(i + 1) % N] + (state[(i + 2) % N][b],))
                == 4
            )
        out.append(tuple(row))
    return tuple(out)


def unorientable(state):
    rels = tuple(relation(state, i) for i in range(N))
    forced = all(sum(sum(row) for row in rel) == 2 for rel in rels)
    return forced and sum(rel[0][1] for rel in rels) % 2 == 1


def closure_score(state):
    total = 0
    for i in range(N):
        left_span = span(state[i])
        right_span = span(state[(i + 2) % N])
        total += sum(x in left_span for x in state[(i + 2) % N])
        total += sum(x in right_span for x in state[i])
    return total


def legal_repartitions(state):
    for i in range(N):
        j = (i + 1) % N
        four_slots = state[i] + state[j]
        for chosen in combinations(range(4), 2):
            chosen = set(chosen)
            left = tuple(four_slots[k] for k in range(4) if k in chosen)
            right = tuple(four_slots[k] for k in range(4) if k not in chosen)
            if is_basis(state[(i - 1) % N], left) and is_basis(right, state[(i + 2) % N]):
                candidate = list(state)
                candidate[i] = left
                candidate[j] = right
                yield tuple(candidate)


RANK2_FLATS = tuple(
    sorted(
        {span(pair) - {0} for pair in PAIRS},
        key=lambda flat: tuple(sorted(flat)),
    )
)
RANK3_FLATS = tuple(
    sorted(
        {
            span(triple) - {0}
            for triple in combinations(VECTORS, 3)
            if rank(triple) == 3
        },
        key=lambda flat: tuple(sorted(flat)),
    )
)


def strict_density(state):
    multiplicity = Counter(x for pair in state for x in pair)
    if max(multiplicity.values()) > 2:
        return False
    if any(sum(multiplicity[x] for x in flat) > 4 for flat in RANK2_FLATS):
        return False
    if any(sum(multiplicity[x] for x in flat) > 7 for flat in RANK3_FLATS):
        return False
    return True


def main():
    compatibility = {
        pair: tuple(other for other in PAIRS if is_basis(pair, other))
        for pair in PAIRS
    }

    admissible_count = 0
    strict_count = 0
    bad_count = 0
    score_histogram = Counter()
    max_gain_histogram = Counter()
    without_increase = 0
    without_direct_orientable_increase = 0
    examples = {}

    for b2 in compatibility[B1]:
        for b3 in compatibility[b2]:
            for b4 in compatibility[b3]:
                if not is_basis(b4, B0):
                    continue
                state = (B0, B1, b2, b3, b4)
                admissible_count += 1
                if not strict_density(state):
                    continue
                strict_count += 1
                if not unorientable(state):
                    continue

                bad_count += 1
                score = closure_score(state)
                score_histogram[score] += 1
                examples.setdefault(score, state)

                increasing = [
                    candidate
                    for candidate in legal_repartitions(state)
                    if closure_score(candidate) > score
                ]
                if not increasing:
                    without_increase += 1
                    continue

                max_gain = max(closure_score(candidate) - score for candidate in increasing)
                max_gain_histogram[max_gain] += 1
                if not any(not unorientable(candidate) for candidate in increasing):
                    without_direct_orientable_increase += 1

    assert len(RANK2_FLATS) == 35
    assert len(RANK3_FLATS) == 15
    assert admissible_count == 49896
    assert strict_count == 43546
    assert bad_count == 80
    assert score_histogram == Counter({2: 40, 4: 40})
    assert max_gain_histogram == Counter({1: 40, 2: 40})
    assert without_increase == 0
    assert without_direct_orientable_increase == 0

    out = {
        "scope": "all normalized admissible N=5 rank-four pair-block configurations over GF(2)^4",
        "normalization": {
            "B0": list(B0),
            "B1": list(B1),
            "reason": "B0 union B1 is a basis, so a GF(2)-linear automorphism sends it to the standard basis",
        },
        "rank_two_flats_checked_for_strict_density": len(RANK2_FLATS),
        "rank_three_flats_checked_for_strict_density": len(RANK3_FLATS),
        "normalized_admissible_configurations": admissible_count,
        "strict_density_configurations": strict_count,
        "strict_unorientable_configurations": bad_count,
        "closure_score_histogram_strict_unorientable": {
            str(k): v for k, v in sorted(score_histogram.items())
        },
        "maximum_score_gain_histogram": {
            str(k): v for k, v in sorted(max_gain_histogram.items())
        },
        "strict_unorientable_without_score_increasing_repartition": without_increase,
        "strict_unorientable_without_direct_score_increasing_orientable_repartition": without_direct_orientable_increase,
        "examples_by_closure_score": {
            str(k): [list(pair) for pair in examples[k]] for k in sorted(examples)
        },
        "status": "exact exhaustive normalized binary N=5 evidence; not a universal closure-potential theorem",
    }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
