#!/usr/bin/env python3
"""Counterexample to full-S4 lexicographic local ascent at binary n=14.

Score:
    (number of blockers, number of valid arbitrary four-block attempts)

The displayed t=0 state satisfies the strict/no-dangerous/universal-two-deletion
package and has no saturated 9-point rank-three flat anywhere. It is bad, has
exactly one distinct CBO-preserving arbitrary-four-block neighbor, no favorable
neighbor, and no lexicographically better neighbor. Nevertheless it reaches
success in two moves, necessarily decreasing blocker count first:

    (7,3) -> (6,7) -> (5,16) and success.

Thus no proof based on local strict ascent of this score can establish the
component theorem.

Finite exact verification of the displayed witness; not Lean certification.
"""

from itertools import combinations, permutations
from collections import Counter, deque
import json

import rank4_binary_n10_nonsimple_exact as base

COLS=(9,13,6,8,3,3,10,11,6,10,4,2,15,14)
E=0
ORDER=(1,8,6,5,13,7,11,3,12,10,2,9,4)
ALL4=tuple(p for p in permutations(range(4)) if p!=(0,1,2,3))


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


def neighbors(order):
    order=tuple(order); m=len(order); out=set()
    for st in range(m):
        inds=[(st+j)%m for j in range(4)]
        vals=[order[i] for i in inds]
        for p in ALL4:
            a=list(order)
            for dst,src in enumerate(p):
                a[inds[dst]]=vals[src]
            t=canonical(a)
            if t!=canonical(order) and cbo(t):
                out.add(t)
    return out


def mobility(order):
    order=tuple(order); m=len(order); out=0
    for st in range(m):
        inds=[(st+j)%m for j in range(4)]
        vals=[order[i] for i in inds]
        for p in ALL4:
            a=list(order)
            for dst,src in enumerate(p):
                a[inds[dst]]=vals[src]
            if cbo(a):
                out += 1
    return out


def bfs():
    start=canonical(ORDER)
    q=deque([start]); prev={start:None}
    while q:
        u=q.popleft()
        for v in neighbors(u):
            if v in prev:
                continue
            prev[v]=u
            if successful(v)[0]:
                path=[v]
                x=u
                while x is not None:
                    path.append(x)
                    x=prev[x]
                path.reverse()
                return path
            q.append(v)
    raise AssertionError("no success in component")


def main():
    assert rank(COLS)==4
    assert profile(range(14))==(2,5,8)

    for D in combinations(range(14),2):
        labs=[i for i in range(14) if i not in D]
        assert rank([COLS[i] for i in labs])==4
        a,b,c=profile(labs)
        assert a<=3 and b<=6 and c<=9

    cnt=Counter(COLS)
    assert max(sum(cnt[x] for x in H) for H in base.HYPERPLANES)==8

    assert cbo(ORDER)
    assert not successful(ORDER)[0]

    ns=neighbors(ORDER)
    assert len(ns)==1
    assert not any(successful(v)[0] for v in ns)

    score0=(blocker_count(ORDER),mobility(ORDER))
    assert score0==(7,3)
    for v in ns:
        assert (blocker_count(v),mobility(v)) <= score0

    path=bfs()
    assert len(path)==3
    scores=[
        (blocker_count(x),mobility(x),successful(x)[0])
        for x in path
    ]
    assert scores==[(7,3,False),(6,7,False),(5,16,True)]

    print(json.dumps({
        "columns":list(COLS),
        "omitted_label":E,
        "deletion_order":list(ORDER),
        "ground_flat_profile":list(profile(range(14))),
        "all_two_deletions_rank_four":True,
        "all_two_deletions_uniform_density_12_over_4":True,
        "has_any_saturated_9_point_rank_three_flat":False,
        "initial_blocker_word":"".join(map(str,blocker_word(ORDER))),
        "initial_score":list(score0),
        "distinct_four_block_neighbors":len(ns),
        "initial_favorable_neighbors":0,
        "lexicographically_better_neighbors":0,
        "fixed_e_distance_to_success":2,
        "shortest_path_scores":[list(x) for x in scores],
        "interpretation":(
            "Even the combined local score (blocker count, full-S4 mobility) "
            "cannot support a strict-ascent proof. The displayed no-saturation "
            "state is a local maximum with no favorable edge, but a shortest "
            "repair path must first decrease blocker count."
        ),
        "claim_level":"exact finite computation; not Lean certification",
    },indent=2,sort_keys=True))


if __name__=="__main__":
    main()
