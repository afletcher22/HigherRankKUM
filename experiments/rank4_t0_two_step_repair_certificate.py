#!/usr/bin/env python3
"""Exact GF(2) certificate for a strict t=0 N=9 obstruction at repair distance 2.

The witness shows that the tempting strengthening

    t = 0 + unorientable admissible pair cycle
      => a one-step orientable 2+2 repair exists

is false.  It does not refute KUM: a two-step repair reaches an orientable
pair cycle, and the resulting flattened order is checked directly.
"""

import json
from itertools import combinations, product

VECTORS = (1, 2, 4, 8, 9, 6, 2, 8, 1, 4, 3, 12, 1, 8, 2, 4, 5, 10)
N = 9
K = 4
INITIAL = tuple((i, i + 1) for i in range(0, 18, 2))
STEP1 = (
    (0, 1), (2, 3), (4, 5), (6, 7), (8, 11),
    (9, 10), (12, 13), (14, 15), (16, 17),
)
STEP2 = (
    (0, 1), (2, 3), (4, 6), (5, 7), (8, 11),
    (9, 10), (12, 13), (14, 15), (16, 17),
)


def rank_values(values):
    pivots = [0] * 4
    r = 0
    for value in values:
        x = value
        while x:
            pivot = x.bit_length() - 1
            if pivots[pivot]:
                x ^= pivots[pivot]
            else:
                pivots[pivot] = x
                r += 1
                break
    return r


def rank_labels(labels):
    return rank_values(VECTORS[i] for i in labels)


def subset_ranks():
    """Exact ranks of all labelled subsets, via GF(2)^4 span bitmasks."""
    size = 1 << len(VECTORS)
    spans = [1] * size  # bit 0 is the zero vector
    ranks = bytearray(size)
    cache = {}
    for mask in range(1, size):
        bit = mask & -mask
        value = VECTORS[bit.bit_length() - 1]
        old = spans[mask ^ bit]
        key = (old, value)
        if key not in cache:
            image = sum(1 << (x ^ value) for x in range(16) if old >> x & 1)
            cache[key] = old | image
        spans[mask] = cache[key]
        ranks[mask] = spans[mask].bit_count().bit_length() - 1
    return ranks


def relation_mask(state, i):
    """Bit 2*x+y records the shifted four-window basis cell."""
    mask = 0
    for x in (0, 1):
        for y in (0, 1):
            labels = (
                state[i][1 - x],
                *state[(i + 1) % N],
                state[(i + 2) % N][y],
            )
            if rank_labels(labels) == 4:
                mask |= 1 << (2 * x + y)
    return mask


def relation_orientable(state):
    masks = tuple(relation_mask(state, i) for i in range(N))
    for bits in product((0, 1), repeat=N):
        if all(
            masks[i] & (1 << (2 * bits[i] + bits[(i + 2) % N]))
            for i in range(N)
        ):
            return bits
    return None


def aligned(state):
    return all(
        rank_labels(state[i] + state[(i + 1) % N]) == 4
        for i in range(N)
    )


def legal_repartitions(state):
    """All nonidentity local 2+2 repair occurrences, boundary-labelled."""
    out = []
    for i in range(N):
        j = (i + 1) % N
        four = state[i] + state[j]
        for chosen_tuple in combinations(range(4), 2):
            chosen = set(chosen_tuple)
            left = tuple(sorted(four[t] for t in range(4) if t in chosen))
            right = tuple(sorted(four[t] for t in range(4) if t not in chosen))
            if (left, right) == (state[i], state[j]):
                continue
            if (
                rank_labels(state[(i - 1) % N] + left) == 4
                and rank_labels(right + state[(i + 2) % N]) == 4
            ):
                candidate = list(state)
                candidate[i], candidate[j] = left, right
                out.append((i, tuple(candidate)))
    return out


def flatten(state, bits):
    return tuple(
        label
        for pair, bit in zip(state, bits)
        for label in (pair[bit], pair[1 - bit])
    )


def cyclic_windows_are_bases(order):
    return all(
        rank_labels(tuple(order[(start + j) % len(order)] for j in range(4))) == 4
        for start in range(len(order))
    )


def main():
    ranks = subset_ranks()
    full = (1 << len(VECTORS)) - 1

    assert ranks[full] == 4
    for mask in range(1, full):
        assert 4 * mask.bit_count() < len(VECTORS) * ranks[mask]

    maxima = {
        r: max(mask.bit_count() for mask, rr in enumerate(ranks) if rr == r)
        for r in (1, 2, 3)
    }
    assert maxima == {1: 3, 2: 7, 3: 12}
    assert maxima[3] < 3 * K + 1  # hence no dangerous rank-three flat

    assert aligned(INITIAL)
    initial_masks = tuple(relation_mask(INITIAL, i) for i in range(N))
    assert all(mask in (6, 9) for mask in initial_masks)
    assert sum(mask == 6 for mask in initial_masks) % 2 == 1
    assert relation_orientable(INITIAL) is None

    repairs = legal_repartitions(INITIAL)
    by_boundary = [sum(i == j for i, _ in repairs) for j in range(N)]
    direct = [(i, s) for i, s in repairs if relation_orientable(s) is not None]
    assert by_boundary == [1] * N
    assert len(repairs) == N
    assert direct == []

    assert any(state == STEP1 for _, state in repairs)
    assert relation_orientable(STEP1) is None
    second = legal_repartitions(STEP1)
    assert any(state == STEP2 for _, state in second)

    orientation = relation_orientable(STEP2)
    assert orientation == (1, 1, 1, 1, 1, 1, 1, 0, 1)
    order = flatten(STEP2, orientation)
    assert sorted(order) == list(range(18))
    assert cyclic_windows_are_bases(order)

    out = {
        "scope": "exact fixed GF(2) N=9 labelled rank-four witness",
        "vectors": list(VECTORS),
        "rank": 4,
        "strict_uniform_density_checked_over_all_subsets": True,
        "max_subset_size_by_rank": {
            "rank1": maxima[1],
            "rank2": maxima[2],
            "rank3": maxima[3],
        },
        "dangerous_hyperplane_count": 0,
        "initial_pairs": [list(pair) for pair in INITIAL],
        "initial_relation_masks": list(initial_masks),
        "initial_relation_orientable": False,
        "nonidentity_legal_repairs_by_boundary": by_boundary,
        "direct_orientable_repairs": len(direct),
        "repair_distance": 2,
        "step1_pairs": [list(pair) for pair in STEP1],
        "step1_relation_masks": [relation_mask(STEP1, i) for i in range(N)],
        "step2_pairs": [list(pair) for pair in STEP2],
        "step2_relation_masks": [relation_mask(STEP2, i) for i in range(N)],
        "final_orientation_bits": list(orientation),
        "final_cbo_labels": list(order),
        "all_final_cyclic_four_windows_are_bases": True,
        "refutes": "t=0 unorientable pair cycle always has a one-step orientable 2+2 repair",
        "does_not_refute": [
            "rank-four KUM",
            "multi-step repair under t=0",
            "existence of a favorable deletion CBO",
        ],
    }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
