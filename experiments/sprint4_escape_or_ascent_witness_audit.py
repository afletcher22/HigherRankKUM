#!/usr/bin/env python3
"""Exact escape-or-ascent audit on the two preserved binary witnesses.

This complements the original Sprint 4 closure-potential audit.  For every
unorientable admissible pair-cycle state in the exact 10-element audit and the
exact 18-element adjacent-exchange component, ask whether there is a legal full
2+2 repair that either

  * is directly orientable, or
  * strictly increases the closure potential Phi.

We also ask whether such a productive repair can be chosen as a genuine cross
repartition (one old element from each modified pair on each new side), and
record the minimum local boundary-closure score at which a productive cross
repair occurs.

The 18-element component contains states that have strict ascent but no direct
one-step orientable repair.  Together with the separately certified binary
N=7 Phi plateau, which has a direct orientable escape but no strict ascent,
this motivates the disjunctive Sprint 4 dynamics theorem.
"""

import json
from collections import Counter, deque
from itertools import combinations, permutations

import sprint4_closure_potential_audit as base


def full_repartition_moves(bases, state):
    """Yield (boundary index, target, kind) for all nontrivial legal repairs."""
    n = len(state)
    for i in range(n):
        j = (i + 1) % n
        ground = tuple(sorted(state[i] + state[j]))
        old_left = set(state[i])
        seen = set()
        for proposed_left in combinations(ground, 2):
            left_set = set(proposed_left)
            left = tuple(sorted(proposed_left))
            right = tuple(sorted(x for x in ground if x not in left_set))
            if not base.pair_union_is_base(bases, state[(i - 1) % n], left):
                continue
            if not base.pair_union_is_base(bases, right, state[(i + 2) % n]):
                continue
            candidate = list(state)
            candidate[i] = left
            candidate[j] = right
            candidate = base.canonical(tuple(candidate))
            if candidate == state or candidate in seen:
                continue
            seen.add(candidate)
            kind = "cross" if len(left_set & old_left) == 1 else "swap"
            yield i, candidate, kind


def refined_stats(vectors, bases, bad_states):
    no_escape_or_ascent = 0
    no_cross_escape_or_ascent = 0
    min_cross_boundary_score = Counter()
    direct_orientable = 0
    strict_ascent = 0
    both = 0
    direct_only = 0
    ascent_only = 0

    for state in bad_states:
        score = base.closure_score(vectors, state)
        has_direct = False
        has_ascent = False
        productive_cross_scores = []

        for i, candidate, kind in full_repartition_moves(bases, state):
            direct = not base.unorientable(bases, candidate)
            ascent = base.closure_score(vectors, candidate) > score
            has_direct = has_direct or direct
            has_ascent = has_ascent or ascent
            if kind == "cross" and (direct or ascent):
                productive_cross_scores.append(
                    sum(base.boundary_closure_counts(vectors, state, i))
                )

        if not (has_direct or has_ascent):
            no_escape_or_ascent += 1
        if productive_cross_scores:
            min_cross_boundary_score[min(productive_cross_scores)] += 1
        else:
            no_cross_escape_or_ascent += 1

        if has_direct:
            direct_orientable += 1
        if has_ascent:
            strict_ascent += 1
        if has_direct and has_ascent:
            both += 1
        elif has_direct:
            direct_only += 1
        elif has_ascent:
            ascent_only += 1

    return {
        "unorientable_states": len(bad_states),
        "with_direct_orientable_repair": direct_orientable,
        "with_strict_phi_ascent": strict_ascent,
        "with_both": both,
        "direct_only": direct_only,
        "ascent_only": ascent_only,
        "without_escape_or_ascent_repair": no_escape_or_ascent,
        "without_productive_cross_repair": no_cross_escape_or_ascent,
        "minimum_productive_cross_boundary_score_histogram": {
            str(k): v for k, v in sorted(min_cross_boundary_score.items())
        },
    }


def ten_element_bad_states():
    vectors = base.TEN_VECTORS
    bases = base.basis_masks(vectors)
    labels = tuple(range(len(vectors)))
    states = set()

    for partner in labels[1:]:
        rest = tuple(x for x in labels[1:] if x != partner)
        for perm in permutations(rest):
            if any(perm[j] > perm[j + 1] for j in range(0, 8, 2)):
                continue
            state = ((0, partner),) + tuple(zip(perm[::2], perm[1::2]))
            if base.admissible(bases, state):
                states.add(base.canonical(state))

    bad = {state for state in states if base.unorientable(bases, state)}
    assert len(states) == 576
    assert len(bad) == 8
    return vectors, bases, bad


def eighteen_element_bad_states():
    vectors = base.EIGHTEEN_VECTORS
    bases = base.basis_masks(vectors)
    start = base.canonical(base.EIGHTEEN_INITIAL)
    seen = {start}
    queue = deque([start])

    while queue:
        state = queue.popleft()
        for neighbor in base.adjacent_exchange_neighbors(bases, state):
            if neighbor not in seen:
                seen.add(neighbor)
                queue.append(neighbor)

    bad = {state for state in seen if base.unorientable(bases, state)}
    assert len(seen) == 30720
    assert len(bad) == 7680
    return vectors, bases, bad


def main():
    ten_vectors, ten_bases, ten_bad = ten_element_bad_states()
    eighteen_vectors, eighteen_bases, eighteen_bad = eighteen_element_bad_states()

    ten = refined_stats(ten_vectors, ten_bases, ten_bad)
    eighteen = refined_stats(eighteen_vectors, eighteen_bases, eighteen_bad)

    assert ten == {
        "unorientable_states": 8,
        "with_direct_orientable_repair": 8,
        "with_strict_phi_ascent": 8,
        "with_both": 8,
        "direct_only": 0,
        "ascent_only": 0,
        "without_escape_or_ascent_repair": 0,
        "without_productive_cross_repair": 0,
        "minimum_productive_cross_boundary_score_histogram": {"0": 8},
    }
    assert eighteen == {
        "unorientable_states": 7680,
        "with_direct_orientable_repair": 6912,
        "with_strict_phi_ascent": 7680,
        "with_both": 6912,
        "direct_only": 0,
        "ascent_only": 768,
        "without_escape_or_ascent_repair": 0,
        "without_productive_cross_repair": 0,
        "minimum_productive_cross_boundary_score_histogram": {
            "1": 4608,
            "2": 3072,
        },
    }

    out = {
        "scope": "exact preserved 10-element audit and exact 18-element repair component",
        "criterion": "one-step relation-orientable escape OR strict closure-potential ascent",
        "ten_element": ten,
        "eighteen_element": eighteen,
        "status": (
            "exact finite evidence for the refined escape-or-ascent dynamics; "
            "not a universal theorem"
        ),
    }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
