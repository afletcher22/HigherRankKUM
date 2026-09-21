#!/usr/bin/env python3
"""Small exact certificate for the Sprint 2 fixed-pair orientation obstruction.

This is intentionally tiny and dependency-free.  It does *not* reproduce the
historical large enumeration.  It verifies one explicit rank-four binary
vector matroid on ten labelled elements.

Vectors are the nonzero columns of GF(2)^4 encoded by integers 1..15.
Repeated vector values at different positions are distinct parallel matroid
elements.
"""

from itertools import product

RANK = 4
PAIRS = ((1, 2), (4, 8), (1, 14), (4, 7), (6, 9))
ELEMENTS = tuple(v for pair in PAIRS for v in pair)


def rank_gf2(columns):
    pivots = [0] * RANK
    rank = 0
    for value in columns:
        x = int(value)
        while x:
            pivot = x.bit_length() - 1
            if pivots[pivot]:
                x ^= pivots[pivot]
            else:
                pivots[pivot] = x
                rank += 1
                break
    return rank


def rank_by_span(columns):
    """Independent rank implementation: |span| = 2^rank over GF(2)."""
    span = {0}
    for value in columns:
        span |= {x ^ int(value) for x in tuple(span)}
    return len(span).bit_length() - 1


def is_basis(columns):
    columns = tuple(columns)
    return len(columns) == RANK and rank_gf2(columns) == RANK


def orientation_relation(i):
    """Relation from orientation of P_i to orientation of P_{i+2}."""
    left = PAIRS[i % 5]
    middle = PAIRS[(i + 1) % 5]
    right = PAIRS[(i + 2) % 5]
    return tuple(
        tuple(
            is_basis((left[1 - a], *middle, right[b]))
            for b in (0, 1)
        )
        for a in (0, 1)
    )


def oriented_sequence(bits):
    out = []
    for pair, bit in zip(PAIRS, bits):
        out.extend((pair[bit], pair[1 - bit]))
    return tuple(out)


def cyclic_order_is_good(sequence):
    n = len(sequence)
    return all(
        is_basis(sequence[(start + j) % n] for j in range(RANK))
        for start in range(n)
    )


def verify_density():
    # Standard rank-four / ten-element density is 2|A| <= 5 r(A).
    # Strict uniform density requires strict inequality for every nonempty
    # proper subset.
    for mask in range(1 << len(ELEMENTS)):
        subset = tuple(
            ELEMENTS[i] for i in range(len(ELEMENTS)) if (mask >> i) & 1
        )
        assert rank_gf2(subset) == rank_by_span(subset)
        if mask == 0 or mask == (1 << len(ELEMENTS)) - 1:
            continue
        assert 2 * len(subset) < 5 * rank_gf2(subset)


def main():
    assert rank_gf2(ELEMENTS) == 4

    # Admissibility for N=5,h=2: every two consecutive pair blocks form a basis.
    for i in range(5):
        assert is_basis(PAIRS[i] + PAIRS[(i + 1) % 5])

    equality = ((True, False), (False, True))
    inequality = ((False, True), (True, False))
    relations = tuple(orientation_relation(i) for i in range(5))
    assert relations == (equality, equality, equality, inequality, equality)

    # The successor is i -> i+2 mod 5.  All relations are forced bijections,
    # and the unique inequality makes their total parity odd.
    assert all(
        not cyclic_order_is_good(oriented_sequence(bits))
        for bits in product((0, 1), repeat=5)
    )

    verify_density()

    print("certified pairs:", PAIRS)
    print("local relations:", relations)
    print("all 32 fixed-pair orientations fail")
    print("all 1022 nonempty proper subsets satisfy strict uniform density")


if __name__ == "__main__":
    main()
