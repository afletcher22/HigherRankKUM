#!/usr/bin/env python3
"""Exact fixed binary N=7 counterexample to universal strict Phi ascent.

The pair cycle below is represented over GF(2)^4.  It is admissible, strictly
uniformly dense, and unorientable at the forced Boolean-relation level.  Its
Sprint 4 closure potential is Phi=10.

We exhaust every legal local full 2+2 repartition at every boundary.  None
strictly increases Phi, so the universal statement

    every non-orientable state has a strictly Phi-increasing repair

is false even in the intended odd-N binary regime.  However an equal-Phi
repair is already orientable.  This is the regression witness motivating the
weaker "direct orientable escape OR strict ascent" dynamics hypothesis.

This certificate concerns one fixed represented matroid/pair cycle.  It is not
a general theorem about arbitrary binary N=7 states.
"""

import json
from collections import Counter
from itertools import combinations

N = 7
VECTORS = tuple(range(1, 16))
PAIRS = tuple(combinations(VECTORS, 2))
STATE = (
    (1, 2),
    (4, 8),
    (13, 14),
    (4, 8),
    (13, 14),
    (5, 9),
    (7, 8),
)


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
                rank(
                    (state[i][1 - a],)
                    + state[(i + 1) % N]
                    + (state[(i + 2) % N][b],)
                )
                == 4
            )
        out.append(tuple(row))
    return tuple(out)


def relation_bit(state, i):
    rel = relation(state, i)
    assert sum(sum(row) for row in rel) == 2
    return int(rel[0][1])


def unorientable(state):
    rels = tuple(relation(state, i) for i in range(N))
    forced = all(sum(sum(row) for row in rel) == 2 for rel in rels)
    return forced and sum(rel[0][1] for rel in rels) % 2 == 1


def closure_edge_scores(state):
    out = []
    for i in range(N):
        left_span = span(state[i])
        right_span = span(state[(i + 2) % N])
        out.append(
            sum(x in left_span for x in state[(i + 2) % N])
            + sum(x in right_span for x in state[i])
        )
    return tuple(out)


def closure_potential(state):
    return sum(closure_edge_scores(state))


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


def flat_occupancy_maxima(state):
    multiplicity = Counter(x for pair in state for x in pair)
    return {
        "rank1": max(multiplicity.values()),
        "rank2": max(sum(multiplicity[x] for x in flat) for flat in RANK2_FLATS),
        "rank3": max(sum(multiplicity[x] for x in flat) for flat in RANK3_FLATS),
    }


def strict_density(state):
    """Strict density for a rank-4 vector matroid on 14 labelled elements."""
    maxima = flat_occupancy_maxima(state)
    # |E|/r(E) = 14/4 = 3.5.  Proper rank-4 subsets are automatic.
    return maxima["rank1"] <= 3 and maxima["rank2"] <= 6 and maxima["rank3"] <= 10


def legal_repartitions_at(state, i):
    """All legal full 2+2 repartitions of blocks i and i+1.

    The middle four-element union is unchanged and hence remains a basis.
    Legality therefore reduces to the two neighboring boundary basis tests.
    """
    j = (i + 1) % N
    four_slots = state[i] + state[j]
    seen = set()
    for chosen_tuple in combinations(range(4), 2):
        chosen = set(chosen_tuple)
        left = tuple(sorted(four_slots[k] for k in range(4) if k in chosen))
        right = tuple(sorted(four_slots[k] for k in range(4) if k not in chosen))
        candidate = list(state)
        candidate[i] = left
        candidate[j] = right
        candidate = tuple(candidate)
        if candidate in seen:
            continue
        seen.add(candidate)
        if is_basis(state[(i - 1) % N], left) and is_basis(right, state[(i + 2) % N]):
            yield candidate


def main():
    assert len(RANK2_FLATS) == 35
    assert len(RANK3_FLATS) == 15
    assert all(is_basis(STATE[i], STATE[(i + 1) % N]) for i in range(N))
    assert strict_density(STATE)
    assert unorientable(STATE)

    score = closure_potential(STATE)
    assert score == 10
    assert closure_edge_scores(STATE) == (0, 4, 4, 0, 0, 0, 2)
    assert tuple(relation_bit(STATE, i) for i in range(N)) == (0, 0, 0, 1, 1, 1, 0)

    moves = []
    distinct_targets = {}
    for i in range(N):
        for candidate in legal_repartitions_at(STATE, i):
            gain = closure_potential(candidate) - score
            orientable = not unorientable(candidate)
            moves.append((i, gain, orientable, candidate))
            distinct_targets[candidate] = (gain, orientable)

    gain_histogram = Counter(gain for _, gain, _, _ in moves)
    assert len(moves) == 12
    assert len(distinct_targets) == 6
    assert gain_histogram == Counter({0: 9, -1: 2, -2: 1})
    assert max(gain for _, gain, _, _ in moves) == 0
    assert not any(gain > 0 for _, gain, _, _ in moves)
    assert any(orientable for _, _, orientable, _ in moves)

    equal_escape = [
        (i, candidate)
        for i, gain, orientable, candidate in moves
        if gain == 0 and orientable and candidate != STATE
    ]
    assert equal_escape
    escape_boundary, escape_state = equal_escape[0]
    assert escape_boundary == 6
    assert escape_state == (
        (1, 7),
        (4, 8),
        (13, 14),
        (4, 8),
        (13, 14),
        (5, 9),
        (2, 8),
    )

    out = {
        "state": [list(pair) for pair in STATE],
        "admissible_adjacent_bases": True,
        "strict_density": True,
        "flat_occupancy_maxima": flat_occupancy_maxima(STATE),
        "relation_bits": [relation_bit(STATE, i) for i in range(N)],
        "unorientable": True,
        "closure_edge_scores": list(closure_edge_scores(STATE)),
        "closure_potential": score,
        "legal_repartition_occurrences": len(moves),
        "distinct_repair_targets": len(distinct_targets),
        "gain_histogram": {
            str(k): v for k, v in sorted(gain_histogram.items())
        },
        "maximum_gain": 0,
        "strictly_increasing_repair_exists": False,
        "direct_orientable_repair_exists": True,
        "equal_potential_orientable_repair_exists": True,
        "equal_potential_orientable_example_boundary": escape_boundary,
        "equal_potential_orientable_example_state": [list(pair) for pair in escape_state],
        "status": (
            "exact fixed binary N=7 counterexample to universal strict "
            "closure-potential ascent; supports escape-or-ascent refinement"
        ),
    }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
