#!/usr/bin/env python3
"""Exact finite audit of a candidate closure-based repair potential.

For a cyclic sequence of pair blocks B_i in the preserved binary rank-four
witnesses, define

  Phi = sum_i (
      |B_{i+1} ∩ cl(B_{i-1})| + |B_i ∩ cl(B_{i+2})|
  ).

These are exactly the two families of neighbor-closure incidences appearing in
the Sprint 3 rank-four local-rigidity obstruction.  In the represented binary
matroids below, closure is computed by vector span.

The purpose of this script is hypothesis generation, not theorem certification:
it asks whether every unorientable state in the two preserved finite audits has
an admissibility-preserving full 2+2 repartition that strictly increases Phi,
and whether repeated strict increases can reach an orientable state.

A positive answer on these witnesses does NOT imply a universal monotone
potential theorem.  In particular, Phi is not even an orientability classifier
on the ten-element witness.
"""

import json
from collections import Counter, deque
from itertools import combinations, permutations


TEN_VECTORS = (1, 2, 4, 8, 1, 14, 4, 7, 6, 9)
TEN_INITIAL = tuple((i, i + 1) for i in range(0, 10, 2))

EIGHTEEN_VECTORS = (1, 2, 4, 8, 1, 6, 2, 8, 1, 4, 2, 12, 1, 8, 2, 4, 5, 8)
EIGHTEEN_INITIAL = tuple((i, i + 1) for i in range(0, 18, 2))


def rank_four(vectors, labels):
    basis = [0] * 4
    rank = 0
    for label in labels:
        x = vectors[label]
        while x:
            pivot = x.bit_length() - 1
            if basis[pivot]:
                x ^= basis[pivot]
            else:
                basis[pivot] = x
                rank += 1
                break
    return rank == 4


def basis_masks(vectors):
    labels = tuple(range(len(vectors)))
    return {
        sum(1 << x for x in block)
        for block in combinations(labels, 4)
        if rank_four(vectors, block)
    }


def canonical(state):
    state = tuple(tuple(sorted(pair)) for pair in state)
    n = len(state)
    pivot = min(range(n), key=state.__getitem__)
    return state[pivot:] + state[:pivot]


def pair_union_is_base(bases, left, right):
    return sum(1 << x for x in left + right) in bases


def admissible(bases, state):
    n = len(state)
    return all(pair_union_is_base(bases, state[i], state[(i + 1) % n]) for i in range(n))


def relation(bases, state, i):
    n = len(state)
    out = []
    for a in (0, 1):
        row = []
        for b in (0, 1):
            labels = (state[i][1 - a],) + state[(i + 1) % n] + (state[(i + 2) % n][b],)
            row.append(sum(1 << x for x in labels) in bases)
        out.append(tuple(row))
    return tuple(out)


def unorientable(bases, state):
    rels = tuple(relation(bases, state, i) for i in range(len(state)))
    forced = all(sum(sum(row) for row in rel) == 2 for rel in rels)
    return forced and sum(rel[0][1] for rel in rels) % 2 == 1


def span_values(vectors, pair):
    a, b = vectors[pair[0]], vectors[pair[1]]
    return {0, a, b, a ^ b}


def boundary_closure_counts(vectors, state, i):
    n = len(state)
    left_span = span_values(vectors, state[(i - 1) % n])
    right_span = span_values(vectors, state[(i + 2) % n])
    left = sum(vectors[x] in left_span for x in state[(i + 1) % n])
    right = sum(vectors[x] in right_span for x in state[i])
    return left, right


def closure_score(vectors, state):
    return sum(
        sum(boundary_closure_counts(vectors, state, i))
        for i in range(len(state))
    )


def saturated_boundary_count(vectors, state):
    return sum(
        any(boundary_closure_counts(vectors, state, i))
        for i in range(len(state))
    )


def full_repartition_neighbors(bases, state):
    n = len(state)
    out = set()
    for i in range(n):
        j = (i + 1) % n
        ground = tuple(sorted(state[i] + state[j]))
        for proposed_left in combinations(ground, 2):
            left_set = set(proposed_left)
            proposed_right = tuple(x for x in ground if x not in left_set)
            left = tuple(sorted(proposed_left))
            right = tuple(sorted(proposed_right))
            if not pair_union_is_base(bases, state[(i - 1) % n], left):
                continue
            if not pair_union_is_base(bases, right, state[(i + 2) % n]):
                continue
            candidate = list(state)
            candidate[i] = left
            candidate[j] = right
            candidate = canonical(tuple(candidate))
            if candidate != state:
                out.add(candidate)
    return out


def adjacent_exchange_neighbors(bases, state):
    n = len(state)
    for i in range(n):
        j = (i + 1) % n
        for a in (0, 1):
            for b in (0, 1):
                left = list(state[i])
                right = list(state[j])
                left[a], right[b] = right[b], left[a]
                left = tuple(sorted(left))
                right = tuple(sorted(right))
                if not pair_union_is_base(bases, state[(i - 1) % n], left):
                    continue
                if not pair_union_is_base(bases, right, state[(i + 2) % n]):
                    continue
                candidate = list(state)
                candidate[i] = left
                candidate[j] = right
                yield canonical(tuple(candidate))


def increasing_path_histogram(vectors, bases, bad):
    bad = set(bad)
    histogram = Counter()
    without_increase = 0
    for state in bad:
        score = closure_score(vectors, state)
        increasing = [
            neighbor
            for neighbor in full_repartition_neighbors(bases, state)
            if closure_score(vectors, neighbor) > score
        ]
        if not increasing:
            without_increase += 1
            continue
        if any(neighbor not in bad for neighbor in increasing):
            histogram[1] += 1
            continue
        found_two_step = False
        for neighbor in increasing:
            next_score = closure_score(vectors, neighbor)
            if any(
                second not in bad and closure_score(vectors, second) > next_score
                for second in full_repartition_neighbors(bases, neighbor)
            ):
                found_two_step = True
                break
        assert found_two_step, "finite witness needs an increasing path longer than two steps"
        histogram[2] += 1
    return without_increase, histogram


def ten_element_audit():
    vectors = TEN_VECTORS
    bases = basis_masks(vectors)
    labels = tuple(range(len(vectors)))
    states = set()

    # Fix the pair containing label 0 first, quotienting cyclic rotation.
    for partner in labels[1:]:
        rest = tuple(x for x in labels[1:] if x != partner)
        for perm in permutations(rest):
            if any(perm[j] > perm[j + 1] for j in range(0, 8, 2)):
                continue
            state = ((0, partner),) + tuple(zip(perm[::2], perm[1::2]))
            if admissible(bases, state):
                states.add(canonical(state))

    bad = {state for state in states if unorientable(bases, state)}
    good = states - bad
    without_increase, path_hist = increasing_path_histogram(vectors, bases, bad)

    assert len(states) == 576
    assert len(bad) == 8
    assert Counter(closure_score(vectors, s) for s in bad) == Counter({4: 8})
    assert Counter(closure_score(vectors, s) for s in good) == Counter({4: 40, 5: 208, 6: 272, 7: 48})
    assert without_increase == 0
    assert path_hist == Counter({1: 8})

    return {
        "admissible_pair_cycles": len(states),
        "unorientable_pair_cycles": len(bad),
        "orientable_pair_cycles": len(good),
        "closure_score_histogram_unorientable": {
            str(k): v for k, v in sorted(Counter(closure_score(vectors, s) for s in bad).items())
        },
        "closure_score_histogram_orientable": {
            str(k): v for k, v in sorted(Counter(closure_score(vectors, s) for s in good).items())
        },
        "unorientable_without_score_increasing_repartition": without_increase,
        "score_increasing_path_to_orientable_histogram": {
            str(k): v for k, v in sorted(path_hist.items())
        },
    }


def eighteen_element_audit():
    vectors = EIGHTEEN_VECTORS
    bases = basis_masks(vectors)
    start = canonical(EIGHTEEN_INITIAL)
    seen = {start}
    queue = deque([start])
    while queue:
        state = queue.popleft()
        for neighbor in adjacent_exchange_neighbors(bases, state):
            if neighbor not in seen:
                seen.add(neighbor)
                queue.append(neighbor)

    bad = {state for state in seen if unorientable(bases, state)}
    good = seen - bad
    without_increase, path_hist = increasing_path_histogram(vectors, bases, bad)

    bad_score = Counter(closure_score(vectors, s) for s in bad)
    good_score = Counter(closure_score(vectors, s) for s in good)
    bad_saturation = Counter(saturated_boundary_count(vectors, s) for s in bad)
    good_saturation = Counter(saturated_boundary_count(vectors, s) for s in good)

    assert len(seen) == 30720
    assert len(bad) == 7680
    assert bad_score == Counter({18: 3072, 20: 4608})
    assert good_score == Counter({21: 9216, 22: 4608, 23: 9216})
    assert bad_saturation == Counter({9: 7680})
    assert good_saturation == Counter({8: 4608, 9: 18432})
    assert without_increase == 0
    assert path_hist == Counter({1: 6912, 2: 768})

    return {
        "component_vertices": len(seen),
        "unorientable_vertices": len(bad),
        "orientable_vertices": len(good),
        "closure_score_histogram_unorientable": {
            str(k): v for k, v in sorted(bad_score.items())
        },
        "closure_score_histogram_orientable": {
            str(k): v for k, v in sorted(good_score.items())
        },
        "closure_saturated_boundary_count_histogram_unorientable": {
            str(k): v for k, v in sorted(bad_saturation.items())
        },
        "closure_saturated_boundary_count_histogram_orientable": {
            str(k): v for k, v in sorted(good_saturation.items())
        },
        "unorientable_without_score_increasing_repartition": without_increase,
        "score_increasing_path_to_orientable_histogram": {
            str(k): v for k, v in sorted(path_hist.items())
        },
    }


def main():
    out = {
        "scope": "two preserved binary rank-four finite witnesses; candidate-potential audit only",
        "potential": "sum_i (|B_(i+1) intersect cl(B_(i-1))| + |B_i intersect cl(B_(i+2))|)",
        "ten_element": ten_element_audit(),
        "eighteen_element": eighteen_element_audit(),
        "status": "exact finite evidence for a closure-ascent repair heuristic; not a universal monotonicity theorem",
    }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
