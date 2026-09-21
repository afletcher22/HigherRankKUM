#!/usr/bin/env python3
"""Counterexample to blocker-count local maximality at binary n=14.

The state below satisfies the strict/no-dangerous/universal-two-deletion t=0
package and has no saturated 9-point rank-three flat anywhere. It is bad,
has no favorable one-step arbitrary-four-block neighbor, and no bad one-step
neighbor with strictly more blockers. Thus blocker count alone is not a valid
local extremal criterion.

However, an equal-blocker plateau move increases seven-move mobility, and the
next move reaches success. This motivates a lexicographic extremal score
(blocker count, seven-move mobility).

Finite exact verification of the displayed witness; not Lean certification.
"""

from itertools import combinations, permutations
from collections import Counter
import json

import rank4_binary_n10_nonsimple_exact as base

COLS=(3,10,4,1,3,13,9,2,15,6,3,8,5,13)
E=0
ORDER=(1,10,9,2,6,12,8,5,4,11,7,13,3)

ALL4=tuple(p for p in permutations(range(4)) if p!=(0,1,2,3))
SEVEN=(
    (1,0,2,3),
    (0,2,1,3),
    (0,1,3,2),
    (2,3,0,1),
    (2,3,1,0),
    (3,1,2,0),
    (0,3,2,1),
)


def rank(vals):
    return base.rank2(vals)


def canonical(order):
    order=tuple(order)
    i=order.index(min(order))
    return order[i:]+order[:i]


def cbo(order):
    m=len(order)
    return all(rank([COLS[order[(i+j)%m]] for j in range(4)])==4
               for i in range(m))


def successful(order):
    for gap in range(len(order)):
        a=list(order); a.insert(gap,E)
        if cbo(a):
            return True,gap
    return False,None


def blocker_word(order):
    m=len(order); bits=[]
    for i in range(m):
        tri=[order[(i+j)%m] for j in range(3)]
        vals=[COLS[x] for x in tri]
        bits.append(int(rank(vals+[COLS[E]])==rank(vals)))
    return tuple(bits)


def blocker_count(order):
    return sum(blocker_word(order))


def profile(labels):
    cnt=Counter(COLS[i] for i in labels)
    def occ(F): return sum(cnt[x] for x in F)
    return (
        max(cnt.values(),default=0),
        max(occ(F) for F in base.LINES),
        max(occ(F) for F in base.HYPERPLANES),
    )


def neighbors(order,patterns):
    order=tuple(order); m=len(order); out=set()
    for st in range(m):
        inds=[(st+j)%m for j in range(4)]
        vals=[order[i] for i in inds]
        for p in patterns:
            a=list(order)
            for dst,src in enumerate(p):
                a[inds[dst]]=vals[src]
            t=canonical(a)
            if t!=canonical(order) and cbo(t):
                out.add(t)
    return out


def seven_mobility(order):
    # Count valid (start, move-type) attempts, not distinct neighbors.
    order=tuple(order); m=len(order); out=0
    for st in range(m):
        inds=[(st+j)%m for j in range(4)]
        vals=[order[i] for i in inds]
        for p in SEVEN:
            a=list(order)
            for dst,src in enumerate(p):
                a[inds[dst]]=vals[src]
            if cbo(a):
                out += 1
    return out


def main():
    assert rank(COLS)==4
    assert profile(range(14))==(3,5,8)

    # Full two-deletion package.
    for D in combinations(range(14),2):
        labs=[i for i in range(14) if i not in D]
        assert rank([COLS[i] for i in labs])==4
        a,b,c=profile(labs)
        assert a<=3 and b<=6 and c<=9

    # No saturated 9-point rank-three flat anywhere.
    cnt=Counter(COLS)
    assert max(sum(cnt[x] for x in H) for H in base.HYPERPLANES)==8

    assert cbo(ORDER)
    assert not successful(ORDER)[0]

    ns=neighbors(ORDER,ALL4)
    assert len(ns)==5
    assert not any(successful(v)[0] for v in ns)

    b0=blocker_count(ORDER)
    assert b0==8
    assert not any(
        (not successful(v)[0]) and blocker_count(v)>b0
        for v in ns
    )

    # The obstruction is only local: one equal-blocker plateau move exists
    # whose seven-move mobility increases and which has a success neighbor.
    plateau=None
    success=None
    for v in ns:
        if blocker_count(v)!=b0 or successful(v)[0]:
            continue
        goods=[w for w in neighbors(v,ALL4) if successful(w)[0]]
        if goods and seven_mobility(v)>seven_mobility(ORDER):
            plateau=v
            success=goods[0]
            break

    assert plateau is not None
    assert blocker_count(plateau)==8
    assert seven_mobility(ORDER)==4
    assert seven_mobility(plateau)==9
    assert successful(success)[0]
    assert blocker_count(success)==7

    print(json.dumps({
        "columns":list(COLS),
        "omitted_label":E,
        "deletion_order":list(ORDER),
        "ground_flat_profile":list(profile(range(14))),
        "all_two_deletions_rank_four":True,
        "all_two_deletions_uniform_density_12_over_4":True,
        "has_any_saturated_9_point_rank_three_flat":False,
        "initial_blocker_word":"".join(map(str,blocker_word(ORDER))),
        "initial_blocker_count":b0,
        "initial_arbitrary_four_block_neighbors":len(ns),
        "initial_favorable_neighbors":0,
        "bad_neighbors_with_more_blockers":0,
        "initial_seven_move_mobility":seven_mobility(ORDER),
        "plateau_order":list(plateau),
        "plateau_blocker_count":blocker_count(plateau),
        "plateau_seven_move_mobility":seven_mobility(plateau),
        "success_order":list(success),
        "success_blocker_count":blocker_count(success),
        "interpretation":(
            "Blocker count alone is not a valid local-maximality theorem. "
            "The displayed bad state is locally maximal in blocker count and "
            "has no favorable one-step four-block neighbor despite having no "
            "saturated flat. It escapes through an equal-blocker plateau move "
            "that raises seven-move mobility from 4 to 9, then reaches success."
        ),
        "claim_level":"exact finite computation; not Lean certification",
    },indent=2,sort_keys=True))


if __name__=="__main__":
    main()
