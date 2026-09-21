#!/usr/bin/env python3
"""Exact GF(2) regression certificate for a strict t=0 unorientable N=7 pair cycle.

This witness refutes the strengthening

    every strict rank-four gcd-two matroid with no dangerous hyperplane has
    every admissible pair cycle relation-orientable.

It does NOT refute KUM or existential orientability after changing the pair
cycle. In fact the same state has several one-step local repartitions that are
already relation-orientable.
"""

from collections import Counter
from itertools import combinations
import json

WITNESS = (
    (4, 12),
    (10, 11),
    (4, 6),
    (10, 15),
    (6, 11),
    (7, 15),
    (3, 14),
)
N = 7
K = 3
VECTORS = tuple(range(1, 16))
PAIRS = tuple(combinations(VECTORS, 2))


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


RANK2_FLATS = tuple(
    sorted({span(pair) - {0} for pair in PAIRS}, key=lambda f: tuple(sorted(f)))
)
RANK3_FLATS = tuple(
    sorted(
        {
            span(triple) - {0}
            for triple in combinations(VECTORS, 3)
            if rank(triple) == 3
        },
        key=lambda f: tuple(sorted(f)),
    )
)


def relation(state, i):
    out = []
    for a in (0, 1):
        row = []
        for b in (0, 1):
            row.append(
                rank(
                    (state[i][1 - a],)
                    + state[(i + 1) % N]
                    + (state[(i + 2) % N][b],)
                )
                == 4
            )
        out.append(tuple(row))
    return tuple(out)


def relation_orientable(state):
    rels = tuple(relation(state, i) for i in range(N))
    for mask in range(1 << N):
        bits = [(mask >> i) & 1 for i in range(N)]
        if all(rels[i][bits[i]][bits[(i + 2) % N]] for i in range(N)):
            return True
    return False


def legal_repartitions(state):
    for i in range(N):
        j = (i + 1) % N
        slots = state[i] + state[j]
        for chosen_tuple in combinations(range(4), 2):
            chosen = set(chosen_tuple)
            left = tuple(slots[t] for t in range(4) if t in chosen)
            right = tuple(slots[t] for t in range(4) if t not in chosen)
            if (
                rank(state[(i - 1) % N] + left) == 4
                and rank(right + state[(i + 2) % N]) == 4
            ):
                candidate = list(state)
                candidate[i] = left
                candidate[j] = right
                yield i, left, right, tuple(candidate)


def main():
    state = WITNESS
    multiplicity = Counter(x for pair in state for x in pair)

    assert rank([x for pair in state for x in pair]) == 4
    assert all(rank(state[i] + state[(i + 1) % N]) == 4 for i in range(N))

    rank1_max = max(multiplicity.values())
    rank2_max = max(
        sum(multiplicity[x] for x in flat) for flat in RANK2_FLATS
    )
    rank3_occupancies = [
        sum(multiplicity[x] for x in flat) for flat in RANK3_FLATS
    ]
    rank3_max = max(rank3_occupancies)

    # Strict rank-four density at |E|=14: caps are 3,6,10 for ranks 1,2,3.
    assert rank1_max <= K
    assert rank2_max <= 2 * K
    assert rank3_max < 3 * K + 1

    dangerous_count = sum(x == 3 * K + 1 for x in rank3_occupancies)
    assert dangerous_count == 0

    rels = tuple(relation(state, i) for i in range(N))
    forced = all(sum(sum(row) for row in rel) == 2 for rel in rels)
    relation_bits = tuple(int(rel[0][1]) for rel in rels)

    assert forced
    assert sum(relation_bits) % 2 == 1
    assert not relation_orientable(state)

    repairs = list(legal_repartitions(state))
    orientable_repairs = [
        (i, left, right, candidate)
        for i, left, right, candidate in repairs
        if relation_orientable(candidate)
    ]

    assert len(repairs) == 14
    assert len(orientable_repairs) == 6

    i, left, right, candidate = orientable_repairs[0]
    out = {
        "scope": "exact fixed GF(2) N=7 labelled rank-four witness",
        "witness": [list(pair) for pair in state],
        "rank": 4,
        "adjacent_pair_unions_are_bases": True,
        "strict_density_caps": {"rank1": K, "rank2": 2 * K, "rank3": 3 * K + 1},
        "rank1_max_occupancy": rank1_max,
        "rank2_max_flat_occupancy": rank2_max,
        "rank3_max_flat_occupancy": rank3_max,
        "dangerous_hyperplane_count": dangerous_count,
        "forced_relation_bits": list(relation_bits),
        "all_local_relations_bijections": forced,
        "relation_parity_odd": True,
        "relation_orientable": False,
        "legal_repartition_occurrences": len(repairs),
        "direct_orientable_repartition_occurrences": len(orientable_repairs),
        "example_direct_orientable_repair": {
            "boundary": i,
            "left": list(left),
            "right": list(right),
            "state": [list(pair) for pair in candidate],
        },
        "refutes": "unorientable admissible pair cycle implies existence of a dangerous hyperplane",
        "does_not_refute": [
            "KUM",
            "existence of another orientable admissible pair cycle",
            "one-step repair under the t=0 hypothesis",
        ],
    }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
