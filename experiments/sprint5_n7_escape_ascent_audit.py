#!/usr/bin/env python3
"""Bounded exhaustive normalized binary seven-pair forced-cycle audit.

Fix the first two pairs to (1,2),(4,8) in GF(2)^4. Enumerate only cycles
whose local orientation relations are forced bijections; odd parity is the
exact obstruction. Repeated vector values remain distinct labelled elements.
This is not an enumeration of all matroids or a universal repair theorem.
"""

import json
from collections import Counter
from itertools import combinations, combinations_with_replacement, product
from functools import lru_cache

PAIRS = tuple(combinations(range(1, 16), 2))
PAIR_INDEX = {pair: i for i, pair in enumerate(PAIRS)}
SPANS = tuple(frozenset((0, a, b, a ^ b)) for a, b in PAIRS)


def rank(values):
    pivots = [0] * 4
    for x in values:
        while x:
            k = x.bit_length() - 1
            if pivots[k]:
                x ^= pivots[k]
            else:
                pivots[k] = x
                break
    return sum(bool(x) for x in pivots)


BASES = frozenset(sum(1 << x for x in c)
                  for c in combinations(range(1, 16), 4) if rank(c) == 4)


def basis(values):
    return sum(1 << x for x in set(values)) in BASES


ADJ = tuple(tuple(j for j, b in enumerate(PAIRS) if basis(a + b))
            for a in PAIRS)
ADJSETS = tuple(frozenset(row) for row in ADJ)


@lru_cache(None)
def relation(a, b, c):
    """Bit 2*x+y is valid iff last(A,x), B, first(C,y) is a basis."""
    return sum(1 << (2*x+y) for x in range(2) for y in range(2)
               if basis((PAIRS[a][1-x],) + PAIRS[b] + (PAIRS[c][y],)))


@lru_cache(None)
def forced_next(a, b):
    return tuple((c, int(relation(a, b, c) == 6)) for c in ADJ[b]
                 if relation(a, b, c) in (6, 9))


EDGE = tuple(tuple(sum(x in SPANS[a] for x in PAIRS[b])
                        + sum(x in SPANS[b] for x in PAIRS[a])
                        for b in range(len(PAIRS)))
             for a in range(len(PAIRS)))


def phi(state):
    return sum(EDGE[a][state[(i+2) % len(state)]] for i, a in enumerate(state))


def bad(state):
    assert len(state) % 2 == 1, 'single-cycle parity criterion requires odd N'
    masks = tuple(relation(state[i], state[(i+1) % len(state)],
                           state[(i+2) % len(state)]) for i in range(len(state)))
    return all(m in (6, 9) for m in masks) and sum(m == 6 for m in masks) % 2 == 1


@lru_cache(None)
def local_replacements(a, b, c, d):
    """All nonidentity full 2+2 choices replacing middle b,c."""
    four = PAIRS[b] + PAIRS[c]
    out = []
    for slots in combinations(range(4), 2):
        left = PAIR_INDEX[tuple(sorted(four[k] for k in slots))]
        right = PAIR_INDEX[tuple(sorted(four[k] for k in range(4) if k not in slots))]
        if (left, right) == (b, c):
            continue
        if left in ADJSETS[a] and d in ADJSETS[right]:
            out.append((left, right))
    return tuple(out)


def moves(state):
    n = len(state)
    for i in range(n):
        j = (i+1) % n
        for left, right in local_replacements(state[(i-1) % n], state[i],
                                               state[j], state[(i+2) % n]):
            target = list(state)
            target[i], target[j] = left, right
            yield i, tuple(target)


def local_effect(state, i, target):
    """Six-block criterion, valid here for odd N >= 5 (indices may overlap).

    Only relation/edge start indices i-2,i-1,i,i+1 are affected. The old
    state must be forced and odd. No global relation scan is used here.
    """
    n = len(state)
    affected = {(i + offset) % n for offset in (-2, -1, 0, 1)}
    old_masks = [relation(state[j], state[(j+1) % n], state[(j+2) % n])
                 for j in affected]
    new_masks = [relation(target[j], target[(j+1) % n], target[(j+2) % n])
                 for j in affected]
    assert all(m in (6, 9) for m in old_masks)
    slack = any(m not in (6, 9) for m in new_masks)
    parity_change = (sum(m == 6 for m in old_masks)
                     + sum(m == 6 for m in new_masks)) % 2
    escape = slack or bool(parity_change)
    delta = sum(EDGE[target[j]][target[(j+2) % n]]
                - EDGE[state[j]][state[(j+2) % n]] for j in affected)
    return escape, delta


def rank_by_span(values):
    """Independent from elimination and the basis lookup table."""
    elements = {0}
    for x in values:
        elements |= {y ^ x for y in tuple(elements)}
    return len(elements).bit_length() - 1


def verify_positive_repair(state, i, target):
    """Reconstruct labelled CBO and test every window with independent rank."""
    n = len(state)
    masks = tuple(relation(target[j], target[(j+1) % n], target[(j+2) % n])
                  for j in range(n))
    bits = next(bits for bits in product(range(2), repeat=n)
                if all(masks[j] & (1 << (2*bits[j]+bits[(j+2) % n]))
                       for j in range(n)))
    labels = [tuple((2*j, 2*j+1)) for j in range(n)]
    next_i = (i+1) % n
    # Four moved vectors are distinct: their union is an aligned basis.
    moved_values = PAIRS[state[i]] + PAIRS[state[next_i]]
    moved_labels = labels[i] + labels[next_i]
    local_labels = dict(zip(moved_values, moved_labels))
    assert len(local_labels) == 4
    labels[i] = tuple(local_labels[x] for x in PAIRS[target[i]])
    labels[next_i] = tuple(local_labels[x] for x in PAIRS[target[next_i]])
    order = tuple(x for pair, bit in zip(labels, bits)
                  for x in (pair[bit], pair[1-bit]))
    vectors = tuple(x for pair in state for x in PAIRS[pair])
    assert sorted(order) == list(range(2*n))
    for start in range(2*n):
        window = tuple(vectors[order[(start+j) % (2*n)]] for j in range(4))
        assert rank_by_span(window) == 4
    return order


def strict_density(state):
    """Check every binary ambient proper nonzero subspace by occupancy."""
    counts = Counter(x for p in state for x in PAIRS[p])
    n = len(state)
    for space, r in FLATS:
        if 2 * sum(counts[x] for x in space) >= n*r:
            return False
    return True


def span(values):
    out = {0}
    for x in values:
        out |= {y ^ x for y in tuple(out)}
    return frozenset(out - {0})


FLATS = tuple((s, r) for r in (1, 2, 3)
              for s in sorted({span(v) for v in combinations(range(1, 16), r)
                               if rank(v) == r}, key=lambda s: tuple(sorted(s))))


def forced_cycles(n):
    """No randomized sampling: each normalized ordered pair cycle once."""
    assert n >= 5 and n % 2 == 1
    start = (PAIR_INDEX[(1, 2)], PAIR_INDEX[(4, 8)])

    def extend(path, parity):
        if len(path) == n:
            if path[0] not in ADJSETS[path[-1]]:
                return
            r1 = relation(path[-2], path[-1], path[0])
            r2 = relation(path[-1], path[0], path[1])
            if r1 in (6, 9) and r2 in (6, 9):
                if parity ^ (r1 == 6) ^ (r2 == 6):
                    yield path
            return
        for c, bit in forced_next(path[-2], path[-1]):
            yield from extend(path + (c,), parity ^ bit)

    yield from extend(start, 0)


def audit(n):
    counts = Counter()
    examples = {}
    move_count = 0
    escape_kinds = Counter()
    bad_move_deltas = Counter()
    for state in forced_cycles(n):
        counts['unorientable'] += 1
        assert bad(state)
        if not strict_density(state):
            counts['not_strict'] += 1
            continue
        counts['strict'] += 1
        score = phi(state)
        direct = ascent = cross_productive = False
        first_cross_escape = None
        for i, target in moves(state):
            escape = not bad(target)
            delta = phi(target) - score
            assert local_effect(state, i, target) == (escape, delta)
            assert all(target[(j+1) % n] in ADJSETS[target[j]] for j in range(n))
            move_count += 1
            gain = delta > 0
            direct |= escape
            ascent |= gain
            cross = target[i] != state[(i+1) % n]
            cross_productive |= ((escape or gain) and cross)
            if escape:
                has_slack = any(relation(target[j], target[(j+1) % n], target[(j+2) % n])
                                not in (6, 9) for j in range(n))
                escape_kinds[('cross' if cross else 'swap') +
                             ('_slack' if has_slack else '_even_forced_parity')] += 1
            else:
                bad_move_deltas[delta] += 1
            if escape and cross and first_cross_escape is None:
                first_cross_escape = (i, target)
        kind = 'both' if direct and ascent else 'escape_only' if direct else 'ascent_only' if ascent else 'FAIL'
        counts[kind] += 1
        if not cross_productive:
            counts['no_productive_cross'] += 1
        if first_cross_escape is not None:
            i, target = first_cross_escape
            order = verify_positive_repair(state, i, target)
            counts['independently_checked_cross_escape_CBOs'] += 1
            examples.setdefault(kind, {'state': tuple(PAIRS[p] for p in state),
                                       'boundary': i, 'target': tuple(PAIRS[p] for p in target),
                                       'CBO_labels': order, 'phi': score,
                                       'target_phi': phi(target)})
        if kind == 'FAIL':
            raise AssertionError(('escape-or-ascent counterexample', state))
    expected = {5: (80, 80, 0), 7: (25152, 24424, 728)}[n]
    assert counts['unorientable'] == counts['strict'] == expected[0]
    assert counts['both'] == expected[1]
    assert counts['escape_only'] == expected[2]
    assert counts['ascent_only'] == counts['FAIL'] == counts['not_strict'] == 0
    assert counts['no_productive_cross'] == 0
    assert counts['independently_checked_cross_escape_CBOs'] == expected[0]
    return {'complete': True, 'N': n,
            'counts': {key: counts[key] for key in
                       ('unorientable', 'strict', 'not_strict', 'both', 'escape_only',
                        'ascent_only', 'FAIL', 'no_productive_cross',
                        'independently_checked_cross_escape_CBOs')},
            'nonidentity_legal_move_occurrences_checked': move_count,
            'orientable_move_kinds': dict(sorted(escape_kinds.items())),
            'nonorientable_move_delta_histogram': dict(sorted(bad_move_deltas.items())),
            'examples': examples}


def main():
    assert Counter(r for _, r in FLATS) == {1: 15, 2: 35, 3: 15}
    # Check all four-column multisets, including repeated parallel columns.
    for values in combinations_with_replacement(range(1, 16), 4):
        assert basis(values) == (rank_by_span(values) == 4)
    # Full support and complete forced-transition enumeration are validated
    # for every admissible triple, not merely those reached in the DFS.
    triple_count = 0
    for a in range(len(PAIRS)):
        for b in ADJ[a]:
            for c in ADJ[b]:
                mask = relation(a, b, c)
                assert mask & 3 and mask & 12 and mask & 5 and mask & 10
                assert ((c, int(mask == 6)) in forced_next(a, b)) == (mask in (6, 9))
                triple_count += 1
    print(json.dumps({'scope': 'normalized represented binary rank-four pair cycles only',
                      'admissible_triples_checked': triple_count,
                      'audits': [audit(5), audit(7)]}, indent=2))


if __name__ == '__main__':
    main()
