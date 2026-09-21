#!/usr/bin/env python3
"""Exact binary audit of the central four-block cross-repair geometry.

Normalize the repaired blocks to C=(1,2), D=(4,8) in GF(2)^4.  Among the
forced six-block contexts A,B,C,D,E,F, first forget the outer blocks A,F and
classify each possible forced center B,C,D,E.

For every legal genuine cross repartition C,D -> Q,R, restore every compatible
forced outer A,F and ask whether the four new relations are all forced.  The
observed classification is all-or-nothing at the center level: a center has no
legal cross repair, every legal cross repair always creates slack, or every
legal cross repair remains forced.  No center mixes the latter two behaviors.

This is exact evidence only for represented binary rank-four centers.  It is
not a representation-free theorem and does not prove global repair existence.
"""

import json

import sprint5_n7_escape_ascent_audit as base


def is_cross(c, d, q, r):
    """Each new pair contains one old-C and one old-D vector."""
    cset, dset = set(base.PAIRS[c]), set(base.PAIRS[d])
    qset, rset = set(base.PAIRS[q]), set(base.PAIRS[r])
    return (len(qset & cset) == len(qset & dset) == 1 and
            len(rset & cset) == len(rset & dset) == 1)


def main():
    c = base.PAIR_INDEX[(1, 2)]
    d = base.PAIR_INDEX[(4, 8)]

    left_neighbors = [
        b for b in base.ADJ[c]
        if base.relation(b, c, d) in (6, 9)
    ]
    right_neighbors = [
        e for e in base.ADJ[d]
        if base.relation(c, d, e) in (6, 9)
    ]

    def outer_as(b):
        return [a for a in base.ADJ[b]
                if base.relation(a, b, c) in (6, 9)]

    def outer_fs(e):
        return [f for f in base.ADJ[e]
                if base.relation(d, e, f) in (6, 9)]

    classification = {
        'all_cross_slack': 0,
        'no_legal_cross': 0,
        'all_cross_forced': 0,
        'mixed': 0,
    }
    all_forced_centers = []

    for b in left_neighbors:
        for e in right_neighbors:
            crosses = [
                (q, r) for q, r in base.local_replacements(b, c, d, e)
                if is_cross(c, d, q, r)
            ]
            if not crosses:
                classification['no_legal_cross'] += 1
                continue

            statuses = set()
            for a in outer_as(b):
                for f in outer_fs(e):
                    for q, r in crosses:
                        new = (
                            base.relation(a, b, q),
                            base.relation(b, q, r),
                            base.relation(q, r, e),
                            base.relation(r, e, f),
                        )
                        statuses.add(all(mask in (6, 9) for mask in new))

            if statuses == {False}:
                classification['all_cross_slack'] += 1
            elif statuses == {True}:
                classification['all_cross_forced'] += 1
                all_forced_centers.append({
                    'B': list(base.PAIRS[b]),
                    'E': list(base.PAIRS[e]),
                    'legal_cross_replacements': [
                        [list(base.PAIRS[q]), list(base.PAIRS[r])]
                        for q, r in crosses
                    ],
                })
            else:
                classification['mixed'] += 1

    assert len(left_neighbors) == len(right_neighbors) == 16
    assert {len(outer_as(b)) for b in left_neighbors} == {16}
    assert {len(outer_fs(e)) for e in right_neighbors} == {16}
    assert classification == {
        'all_cross_slack': 161,
        'no_legal_cross': 81,
        'all_cross_forced': 14,
        'mixed': 0,
    }

    print(json.dumps({
        'complete': True,
        'scope': 'normalized binary rank-four forced center geometries with C=(1,2), D=(4,8)',
        'forced_left_neighbor_choices': len(left_neighbors),
        'forced_right_neighbor_choices': len(right_neighbors),
        'center_geometries': len(left_neighbors) * len(right_neighbors),
        'compatible_outer_A_per_B': sorted({len(outer_as(b)) for b in left_neighbors}),
        'compatible_outer_F_per_E': sorted({len(outer_fs(e)) for e in right_neighbors}),
        'classification': classification,
        'all_cross_forced_centers': all_forced_centers,
        'status': ('exact binary center dichotomy: no center has a mix of '
                   'forced-preserving and slack-creating legal cross repairs '
                   'across compatible outer contexts'),
    }, indent=2))


if __name__ == '__main__':
    main()
