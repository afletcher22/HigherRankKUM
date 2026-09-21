#!/usr/bin/env python3
"""Exact local binary audit; no global cycle or density is assumed.

Normalize middle blocks C=(1,2), D=(4,8) of A,B,C,D,E,F. Require every
adjacent union to be a basis and the four old triple relations to be forced.
Exhaust every legal nonidentity C,D -> Q,R repartition. Ask whether all four
new relations can remain forced while their combined parity changes.
"""

import json
from collections import Counter

import sprint5_n7_escape_ascent_audit as base


def main():
    c, d = base.PAIR_INDEX[(1, 2)], base.PAIR_INDEX[(4, 8)]
    left_contexts = []
    for b in base.ADJ[c]:
        if base.relation(b, c, d) not in (6, 9):
            continue
        for a in base.ADJ[b]:
            if base.relation(a, b, c) in (6, 9):
                left_contexts.append((a, b))
    right_contexts = [(e, f) for e, _ in base.forced_next(c, d)
                      for f, _ in base.forced_next(d, e)]
    counts = Counter()
    deltas = Counter()
    first_flip = None
    for a, b in left_contexts:
        for e, f in right_contexts:
            counts['six_block_contexts'] += 1
            old = (base.relation(a,b,c), base.relation(b,c,d),
                   base.relation(c,d,e), base.relation(d,e,f))
            assert all(mask in (6, 9) for mask in old)
            old_parity = sum(mask == 6 for mask in old) % 2
            for q, r in base.local_replacements(b,c,d,e):
                counts['legal_nonidentity_moves'] += 1
                new = (base.relation(a,b,q), base.relation(b,q,r),
                       base.relation(q,r,e), base.relation(r,e,f))
                assert all(mask & 3 and mask & 12 and mask & 5 and mask & 10
                           for mask in new)
                if any(mask not in (6, 9) for mask in new):
                    counts['slack_created'] += 1
                    continue
                counts['forced_preserving_moves'] += 1
                delta = (base.EDGE[a][q] + base.EDGE[b][r] + base.EDGE[q][e]
                         + base.EDGE[r][f] - base.EDGE[a][c] - base.EDGE[b][d]
                         - base.EDGE[c][e] - base.EDGE[d][f])
                deltas[delta] += 1
                if sum(mask == 6 for mask in new) % 2 != old_parity:
                    counts['forced_parity_flips'] += 1
                    if first_flip is None:
                        first_flip = {'old': [base.PAIRS[x] for x in (a,b,c,d,e,f)],
                                      'replacement': [base.PAIRS[q],base.PAIRS[r]],
                                      'old_masks':old, 'new_masks':new}
    assert len(left_contexts) == len(right_contexts) == 256
    assert counts['six_block_contexts'] == 65536
    assert counts['legal_nonidentity_moves'] == 74752
    assert counts['forced_preserving_moves'] == 5120
    assert counts['slack_created'] == 69632
    assert counts['forced_parity_flips'] == 0 and first_flip is None
    assert deltas == {-8: 4, -6: 32, -4: 368, -2: 1248, 0: 1816,
                      2: 1248, 4: 368, 6: 32, 8: 4}
    print(json.dumps({'complete': True,
                      'scope': 'all normalized binary rank-four forced six-block contexts',
                      'left_contexts': len(left_contexts),
                      'right_contexts': len(right_contexts),
                      'counts': {key: counts[key] for key in
                                 ('six_block_contexts', 'legal_nonidentity_moves',
                                  'forced_preserving_moves', 'slack_created', 'forced_parity_flips')},
                      'forced_preserving_local_phi_delta_histogram': dict(sorted(deltas.items())),
                      'first_parity_flip': first_flip}, indent=2))


if __name__ == '__main__':
    main()
