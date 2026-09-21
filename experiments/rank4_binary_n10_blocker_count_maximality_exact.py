#!/usr/bin/env python3
"""Exact blocker-count maximality audit for binary n=10 t=0.

For every pointed representative in the complete binary n=10 class satisfying
the exact two-deletion caps (2,4,6):

  * enumerate every deletion CBO;
  * keep every bad state;
  * connect by arbitrary CBO-preserving permutations of four consecutive
    positions, with the omitted element fixed;
  * call a bad state blocker-maximal if no bad one-step neighbor has strictly
    more blocker positions;
  * among blocker-maximal bad states with no favorable one-step neighbor,
    test whether a visible blocker triple has a saturated 6-point rank-three
    closure through the omitted element.

Finite exact computation; not Lean certification.
"""

from collections import Counter
from itertools import permutations
import json

import rank4_binary_n10_nonsimple_exact as base

ALL4=tuple(p for p in permutations(range(4)) if p!=(0,1,2,3))


def canonical(order):
    order=tuple(order)
    i=order.index(min(order))
    return order[i:]+order[:i]


def blockers(columns,e,order):
    m=len(order); out=[]
    for i in range(m):
        tri=[order[(i+j)%m] for j in range(3)]
        vals=tuple(columns[x] for x in tri)
        if base.rank2(vals+(columns[e],)) == base.rank2(vals):
            out.append(i)
    return out


def blocker_count(columns,e,order):
    return len(blockers(columns,e,order))


def closure_labels(columns,S):
    vals=[columns[i] for i in S]
    r=base.rank2(vals)
    return frozenset(
        i for i,v in enumerate(columns)
        if base.rank2(vals+[v]) == r
    )


def visible_saturated_blocker(columns,e,order):
    for i in blockers(columns,e,order):
        tri=[order[(i+j)%len(order)] for j in range(3)]
        H=closure_labels(columns,tri)
        if e in H and len(H)==6 and base.rank2([columns[x] for x in H])==3:
            return True
    return False


def successful(columns,e,order):
    for gap in range(len(order)):
        a=list(order); a.insert(gap,e)
        if base.cbo(tuple(a),columns):
            return True
    return False


def neighbors(order,states):
    m=len(order); out=set()
    for start in range(m):
        inds=[(start+j)%m for j in range(4)]
        vals=[order[i] for i in inds]
        for patt in ALL4:
            a=list(order)
            for dst,src in enumerate(patt):
                a[inds[dst]]=vals[src]
            t=canonical(a)
            if t in states and t!=order:
                out.add(t)
    return out


def audit_pointed(columns,e):
    states=set(base.deletion_cbos(columns,e))
    good={o:successful(columns,e,o) for o in states}
    bcount={o:blocker_count(columns,e,o) for o in states}

    bad_local_max=0
    bad_local_max_without_success_neighbor=0
    failures=[]

    for o in states:
        if good[o]:
            continue
        ns=neighbors(o,states)
        higher_bad=any((not good[v]) and bcount[v]>bcount[o] for v in ns)
        if higher_bad:
            continue
        bad_local_max += 1
        has_success_neighbor=any(good[v] for v in ns)
        if has_success_neighbor:
            continue
        bad_local_max_without_success_neighbor += 1
        if not visible_saturated_blocker(columns,e,o):
            failures.append({
                "order":list(o),
                "blockers":blockers(columns,e,o),
                "blocker_count":bcount[o],
            })

    return {
        "bad_blocker_count_local_maxima":bad_local_max,
        "local_maxima_without_success_neighbor":
            bad_local_max_without_success_neighbor,
        "local_maxima_without_success_or_visible_saturation":len(failures),
        "failures":failures,
    }


def main():
    patterns,_=base.qualifying_patterns()
    reps=base.orbit_representatives(patterns)
    assert len(reps)==16

    totals=Counter()
    rows=[]
    for oi,(counts,orbit_size) in enumerate(reps):
        columns=base.labelled_columns(counts)
        pointed=[]
        for e in range(10):
            row=audit_pointed(columns,e)
            pointed.append({"omitted_label":e,**row})
            totals["bad_blocker_count_local_maxima"] += row[
                "bad_blocker_count_local_maxima"]
            totals["local_maxima_without_success_neighbor"] += row[
                "local_maxima_without_success_neighbor"]
            totals["local_maxima_without_success_or_visible_saturation"] += row[
                "local_maxima_without_success_or_visible_saturation"]
        rows.append({
            "orbit_index":oi,
            "orbit_size":orbit_size,
            "multiplicity_vector":list(counts),
            "bad_blocker_count_local_maxima":sum(
                x["bad_blocker_count_local_maxima"] for x in pointed),
            "local_maxima_without_success_neighbor":sum(
                x["local_maxima_without_success_neighbor"] for x in pointed),
            "local_maxima_without_success_or_visible_saturation":sum(
                x["local_maxima_without_success_or_visible_saturation"]
                for x in pointed),
            "pointed":pointed,
        })

    assert totals["bad_blocker_count_local_maxima"]==21744
    assert totals["local_maxima_without_success_neighbor"]==1556
    assert totals["local_maxima_without_success_or_visible_saturation"]==0

    print(json.dumps({
        "scope":(
            "complete binary represented n=10 class satisfying exact "
            "two-deletion flat caps (2,4,6)"
        ),
        "move_set":(
            "arbitrary CBO-preserving permutations of four consecutive "
            "positions; omitted element fixed"
        ),
        "bad_blocker_count_local_maxima":
            totals["bad_blocker_count_local_maxima"],
        "local_maxima_without_success_neighbor":
            totals["local_maxima_without_success_neighbor"],
        "local_maxima_without_success_or_visible_saturation":
            totals["local_maxima_without_success_or_visible_saturation"],
        "orbits":rows,
        "interpretation":(
            "Blocker count is not a monotone repair potential, but exact "
            "binary n=10 supports a maximal-placement theorem: every bad "
            "state that is locally maximal for blocker count either has a "
            "favorable one-step four-block neighbor or already exposes a "
            "saturated blocker closure."
        ),
        "claim_level":"exact finite computation; not Lean certification",
    },indent=2,sort_keys=True))


if __name__=="__main__":
    main()
