#!/usr/bin/env python3
"""Exact represented six-block forced-parity audit over GF(2), GF(3), GF(5).

Normalize the middle blocks C,D of A,B,C,D,E,F to the four coordinate
points of PG(3,q). This is exhaustive for q-representable local contexts:
C union D is a basis, so row operations send those four columns to the
coordinate basis, and independent nonzero column scalings do not change the
represented matroid. Repeated projective points in different blocks are
allowed; the two entries of one block are distinct because every adjacent
two-block union is a basis.

For every old context whose adjacent two-block unions are bases and whose
four old endpoint relations are forced bijections, exhaust every legal
nonidentity repartition C,D -> Q,R. Count whether all four new relations
remain forced and, if so, whether their combined Boolean parity changes.

The GF(2) totals independently reproduce sprint5_six_block_parity_audit.py.
GF(3) and GF(5) are exact extensions beyond binary representability.
"""

from collections import Counter
from functools import lru_cache
from itertools import combinations, product
import json

FORCED = (6, 9)


def audit_field(p):
    def canonical(v):
        v = tuple(x % p for x in v)
        first = next(x for x in v if x)
        inv = pow(first, -1, p)
        return tuple((x * inv) % p for x in v)

    points = []
    for v in product(range(p), repeat=4):
        if not any(v):
            continue
        if canonical(v) == v:
            points.append(v)
    points = tuple(points)
    point_index = {v: i for i, v in enumerate(points)}

    def add(*vectors):
        return tuple(sum(v[j] for v in vectors) % p for j in range(4))

    def scale(a, v):
        return tuple((a * x) % p for x in v)

    def rank_ids(ids):
        matrix = [list(points[i]) for i in ids]
        rank = 0
        for col in range(4):
            pivot = next((i for i in range(rank, len(matrix))
                          if matrix[i][col] % p), None)
            if pivot is None:
                continue
            matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
            inv = pow(matrix[rank][col], -1, p)
            matrix[rank] = [(x * inv) % p for x in matrix[rank]]
            for i in range(rank + 1, len(matrix)):
                if matrix[i][col] % p:
                    factor = matrix[i][col] % p
                    matrix[i] = [
                        (matrix[i][j] - factor * matrix[rank][j]) % p
                        for j in range(4)
                    ]
            rank += 1
            if rank == len(matrix):
                break
        return rank

    @lru_cache(None)
    def basis4_sorted(ids):
        return rank_ids(ids) == 4

    def basis4(ids):
        if len(set(ids)) < 4:
            return False
        return basis4_sorted(tuple(sorted(ids)))

    def pair(x, y):
        return tuple(sorted((x, y)))

    standard = (
        point_index[(1, 0, 0, 0)],
        point_index[(0, 1, 0, 0)],
        point_index[(0, 0, 1, 0)],
        point_index[(0, 0, 0, 1)],
    )
    C = pair(standard[0], standard[1])
    D = pair(standard[2], standard[3])

    def forced_partners(middle, reference):
        """All endpoint pairs forced against reference through middle.

        Modulo span(middle), a forced partner has one point on each of the
        two projective lines determined by reference. Each lift has q^2
        choices, giving q^4 unordered pair types in total.
        """
        m0, m1 = (points[i] for i in middle)
        r0, r1 = (points[i] for i in reference)
        families = []
        for r in (r0, r1):
            family = []
            for a in range(p):
                for b in range(p):
                    v = add(r, scale(a, m0), scale(b, m1))
                    family.append(point_index[canonical(v)])
            assert len(set(family)) == p * p
            families.append(family)
        out = {pair(x, y) for x in families[0] for y in families[1]}
        assert len(out) == p ** 4
        return tuple(sorted(out))

    @lru_cache(None)
    def relation(A, B, C_):
        """Bit 2*x+y records the basis test last(A,x), B, first(C,y)."""
        mask = 0
        for x in (0, 1):
            for y in (0, 1):
                if basis4((A[1 - x], B[0], B[1], C_[y])):
                    mask |= 1 << (2 * x + y)
        return mask

    Bs = forced_partners(C, D)
    Es = forced_partners(D, C)
    assert all(basis4(b + C) and relation(b, C, D) in FORCED for b in Bs)
    assert all(basis4(D + e) and relation(C, D, e) in FORCED for e in Es)

    four = C + D
    partitions = []
    for slots in combinations(range(4), 2):
        Q = pair(four[slots[0]], four[slots[1]])
        other = [four[k] for k in range(4) if k not in slots]
        R = pair(other[0], other[1])
        if (Q, R) != (C, D):
            partitions.append((Q, R))
    assert len(partitions) == 5

    def epsilon(mask):
        assert mask in FORCED
        return int(mask == 6)

    # Endpoint contexts factor once b,e,Q,R are fixed. Precompute the exact
    # parity-delta distribution on each side instead of iterating q^16 full
    # six-block contexts individually.
    left_stats = {}
    for b in Bs:
        As = forced_partners(b, C)
        for Q, _ in partitions:
            deltas = Counter()
            witness = {}
            for A in As:
                new = relation(A, b, Q)
                if new in FORCED:
                    delta = epsilon(relation(A, b, C)) ^ epsilon(new)
                    deltas[delta] += 1
                    witness.setdefault(delta, A)
            left_stats[(b, Q)] = (deltas, witness)

    right_stats = {}
    for e in Es:
        Fs = forced_partners(e, D)
        for _, R in partitions:
            deltas = Counter()
            witness = {}
            for F in Fs:
                new = relation(R, e, F)
                if new in FORCED:
                    delta = epsilon(relation(D, e, F)) ^ epsilon(new)
                    deltas[delta] += 1
                    witness.setdefault(delta, F)
            right_stats[(e, R)] = (deltas, witness)

    counts = Counter()
    first_flip = None
    endpoint_contexts_per_middle_pair = p ** 8

    for b in Bs:
        old2 = relation(b, C, D)
        for e in Es:
            old3 = relation(C, D, e)
            for Q, R in partitions:
                if not basis4(b + Q) or not basis4(R + e):
                    continue
                counts['legal_nonidentity_move_occurrences'] += \
                    endpoint_contexts_per_middle_pair

                new2, new3 = relation(b, Q, R), relation(Q, R, e)
                if new2 not in FORCED or new3 not in FORCED:
                    counts['slack_created'] += endpoint_contexts_per_middle_pair
                    continue

                left_delta, left_witness = left_stats[(b, Q)]
                right_delta, right_witness = right_stats[(e, R)]
                forced_here = sum(left_delta.values()) * sum(right_delta.values())
                counts['forced_preserving_move_occurrences'] += forced_here
                counts['slack_created'] += \
                    endpoint_contexts_per_middle_pair - forced_here

                middle_delta = (epsilon(old2) ^ epsilon(new2) ^
                                epsilon(old3) ^ epsilon(new3))
                for ld, left_count in left_delta.items():
                    for rd, right_count in right_delta.items():
                        if ld ^ middle_delta ^ rd:
                            flips = left_count * right_count
                            counts['forced_parity_flips'] += flips
                            if first_flip is None:
                                A = left_witness[ld]
                                F = right_witness[rd]
                                first_flip = {
                                    'old_pairs': [A, b, C, D, e, F],
                                    'replacement': [Q, R],
                                    'old_masks': [
                                        relation(A, b, C), old2, old3,
                                        relation(D, e, F),
                                    ],
                                    'new_masks': [
                                        relation(A, b, Q), new2, new3,
                                        relation(R, e, F),
                                    ],
                                }

    left_contexts = p ** 8
    right_contexts = p ** 8
    assert (counts['forced_preserving_move_occurrences'] +
            counts['slack_created'] ==
            counts['legal_nonidentity_move_occurrences'])

    return {
        'field_order': p,
        'projective_points': len(points),
        'unordered_projective_pair_types': len(points) * (len(points) - 1) // 2,
        'left_middle_types': len(Bs),
        'right_middle_types': len(Es),
        'left_contexts': left_contexts,
        'right_contexts': right_contexts,
        'six_block_contexts': left_contexts * right_contexts,
        'legal_nonidentity_move_occurrences':
            counts['legal_nonidentity_move_occurrences'],
        'forced_preserving_move_occurrences':
            counts['forced_preserving_move_occurrences'],
        'slack_created': counts['slack_created'],
        'forced_parity_flips': counts['forced_parity_flips'],
        'first_parity_flip': first_flip,
    }


def main():
    results = [audit_field(p) for p in (2, 3, 5)]
    binary, ternary, quinary = results

    # Independent regression against sprint5_six_block_parity_audit.py.
    assert binary['left_contexts'] == binary['right_contexts'] == 256
    assert binary['six_block_contexts'] == 65536
    assert binary['legal_nonidentity_move_occurrences'] == 74752
    assert binary['forced_preserving_move_occurrences'] == 5120
    assert binary['slack_created'] == 69632

    assert ternary['left_contexts'] == ternary['right_contexts'] == 6561
    assert ternary['six_block_contexts'] == 43046721
    assert ternary['legal_nonidentity_move_occurrences'] == 91644048
    assert ternary['forced_preserving_move_occurrences'] == 1364688
    assert ternary['slack_created'] == 90279360

    assert quinary['left_contexts'] == quinary['right_contexts'] == 390625
    assert quinary['six_block_contexts'] == 152587890625
    assert quinary['legal_nonidentity_move_occurrences'] == 480625000000
    assert quinary['forced_preserving_move_occurrences'] == 1025000000
    assert quinary['slack_created'] == 479600000000

    for result in results:
        assert result['forced_parity_flips'] == 0
        assert result['first_parity_flip'] is None

    print(json.dumps({
        'complete': True,
        'scope': 'all normalized GF(2), GF(3), and GF(5) rank-four forced six-block represented contexts',
        'normalization': 'C union D is sent to the coordinate basis; all projective lifts are exhausted',
        'fields': results,
    }, indent=2))


if __name__ == '__main__':
    main()
