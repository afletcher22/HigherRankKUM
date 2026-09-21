#!/usr/bin/env python3
"""Exact fixed-e four-block audit for the binary n=10 t=0 class.

Uses the exact two-deletion-robust binary n=10 census from
rank4_binary_n10_nonsimple_exact.py:

  * 28,476 multiplicity patterns;
  * 16 GL(4,2) orbits.

For each orbit representative and each labelled omitted element e:

  1. enumerate every deletion CBO modulo rotation;
  2. build the graph using ONLY CBO-preserving permutations of four
     cyclically consecutive positions;
  3. do NOT allow omitted-element pivots;
  4. check every connected component contains an insertion-successful CBO;
  5. compute the exact maximum graph distance to success.

This directly tests the stronger t=0-specific idea that one can repair while
keeping the omitted element fixed.

Finite exact computation; not Lean certification.
"""

from collections import deque
from itertools import permutations
import json

import rank4_binary_n10_nonsimple_exact as base

ALL4 = tuple(p for p in permutations(range(4)) if p != (0,1,2,3))


def canonical(order):
    order = tuple(order)
    i = order.index(min(order))
    return order[i:] + order[:i]


def successful(columns, omitted, order):
    for gap in range(len(order)):
        full = list(order)
        full.insert(gap, omitted)
        if base.cbo(tuple(full), columns):
            return True
    return False


def audit_fixed_e(columns, omitted):
    orders = set(base.deletion_cbos(columns, omitted))
    good = {o: successful(columns, omitted, o) for o in orders}
    adj = {o: set() for o in orders}

    for order in orders:
        m = len(order)
        for start in range(m):
            inds = [(start + j) % m for j in range(4)]
            old = [order[i] for i in inds]
            for patt in ALL4:
                a = list(order)
                for dst, src in enumerate(patt):
                    a[inds[dst]] = old[src]
                t = canonical(a)
                if t in orders:
                    adj[order].add(t)
                    adj[t].add(order)

    unseen = set(orders)
    comps = []
    closed_bad = []
    while unseen:
        root = unseen.pop()
        comp = {root}
        stack = [root]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if v not in comp:
                    comp.add(v)
                    unseen.discard(v)
                    stack.append(v)
        comps.append(comp)
        if not any(good[x] for x in comp):
            closed_bad.append(comp)

    if closed_bad:
        maxdist = None
    else:
        maxdist = 0
        for comp in comps:
            dist = {x: 0 for x in comp if good[x]}
            q = deque(dist)
            while q:
                u = q.popleft()
                for v in adj[u]:
                    if v in comp and v not in dist:
                        dist[v] = dist[u] + 1
                        q.append(v)
            assert len(dist) == len(comp)
            maxdist = max(maxdist, max(dist.values()))

    return {
        "deletion_cbos": len(orders),
        "successful_cbos": sum(good.values()),
        "components": len(comps),
        "closed_all_bad_components": len(closed_bad),
        "component_sizes": sorted((len(c) for c in comps), reverse=True),
        "maximum_distance_to_success": maxdist,
    }


def main():
    patterns, _ = base.qualifying_patterns()
    assert len(patterns) == 28476
    reps = base.orbit_representatives(patterns)
    assert len(reps) == 16
    assert sum(size for _, size in reps) == 28476

    rows = []
    total_closed_bad = 0
    global_maxdist = 0

    for oi, (counts, orbit_size) in enumerate(reps):
        columns = base.labelled_columns(counts)
        pointed = []
        for e in range(10):
            row = audit_fixed_e(columns, e)
            pointed.append({"omitted_label": e, **row})
            total_closed_bad += row["closed_all_bad_components"]
            if row["maximum_distance_to_success"] is not None:
                global_maxdist = max(
                    global_maxdist, row["maximum_distance_to_success"]
                )

        rows.append({
            "orbit_index": oi,
            "orbit_size": orbit_size,
            "multiplicity_vector": list(counts),
            "maximum_fixed_e_components":
                max(x["components"] for x in pointed),
            "maximum_fixed_e_repair_distance":
                max(x["maximum_distance_to_success"] for x in pointed),
            "total_closed_all_bad_fixed_e_components":
                sum(x["closed_all_bad_components"] for x in pointed),
            "pointed": pointed,
        })

    assert total_closed_bad == 0

    print(json.dumps({
        "scope": (
            "complete binary represented n=10 class satisfying exact "
            "two-deletion flat caps (2,4,6)"
        ),
        "multiplicity_patterns": 28476,
        "gl4_2_orbits": 16,
        "pointed_orbit_representatives": 160,
        "moves": (
            "arbitrary CBO-preserving permutations of four consecutive "
            "positions only; omitted element fixed"
        ),
        "closed_all_bad_fixed_e_components": total_closed_bad,
        "maximum_fixed_e_distance_to_success": global_maxdist,
        "orbits": rows,
        "interpretation": (
            "Point pivots are unnecessary for existence throughout the exact "
            "binary n=10 two-deletion-robust class. Every fixed-e four-block "
            "component contains a successful CBO. The exact worst repair "
            "distance is four, so pivots can shorten paths but are not needed "
            "to reach success."
        ),
        "claim_level": "exact finite computation; not Lean certification",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
