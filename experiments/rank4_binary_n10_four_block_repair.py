#!/usr/bin/env python3
"""Exact binary n=10 audit of two canonical four-block repair moves.

This builds on rank4_binary_n10_nonsimple_exact.py.

State:
    (e, sigma)
where sigma is a CBO of M\e.

Moves:
  1. cyclic adjacent swaps preserving the deletion CBO;
  2. point pivots exchanging the omitted element with one order entry when
     the new deletion order is a CBO;
  3. on four consecutive positions [a,b,c,d], either
         [a,b,c,d] -> [c,d,a,b]
     or
         [a,b,c,d] -> [c,d,b,a],
     whenever the resulting deletion order is a CBO.

The first four-block move swaps two adjacent pairs.  The second swaps the
pairs and reverses the old left pair.  Both are rank-4 / 2+2-scale moves.

For all 16 GL(4,2)-orbits in the exact binary n=10 two-deletion-robust class,
the resulting joint state graph is connected.

Finite computation only; not Lean certification.
"""

from collections import Counter
from itertools import combinations
import json

import rank4_binary_n10_nonsimple_exact as base

FOUR_BLOCK_PATTERNS = (
    (2, 3, 0, 1),  # [a,b,c,d] -> [c,d,a,b]
    (2, 3, 1, 0),  # [a,b,c,d] -> [c,d,b,a]
)


def audit(columns):
    states, cbo_counts = base.states(columns)
    good = {s: base.successful(columns, s) for s in states}
    adj = {s: set() for s in states}

    for e, order in states:
        m = len(order)

        # Adjacent cyclic swaps.
        for i in range(m):
            j = (i + 1) % m
            a = list(order)
            a[i], a[j] = a[j], a[i]
            t = (e, base.canonical(a))
            if t in states:
                adj[(e, order)].add(t)
                adj[t].add((e, order))

        # Point pivots.
        for i, f in enumerate(order):
            a = list(order)
            a[i] = e
            t = (f, base.canonical(a))
            if t in states:
                adj[(e, order)].add(t)
                adj[t].add((e, order))

        # Two canonical consecutive four-block repairs.
        for patt in FOUR_BLOCK_PATTERNS:
            for start in range(m):
                inds = [(start + j) % m for j in range(4)]
                vals = [order[i] for i in inds]
                a = list(order)
                for dst, src in enumerate(patt):
                    a[inds[dst]] = vals[src]
                t = (e, base.canonical(a))
                if t in states:
                    adj[(e, order)].add(t)
                    adj[t].add((e, order))

    unseen = set(states)
    comps = []
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

    return {
        "states": len(states),
        "successful_states": sum(good.values()),
        "components": len(comps),
        "largest_component": max(map(len, comps)),
        "closed_all_bad_components":
            sum(not any(good[s] for s in comp) for comp in comps),
        "deletion_cbos_per_label": cbo_counts,
    }


def main():
    patterns, _ = base.qualifying_patterns()
    reps = base.orbit_representatives(patterns)
    assert len(reps) == 16

    rows = []
    for oi, (counts, orbit_size) in enumerate(reps):
        columns = base.labelled_columns(counts)
        row = audit(columns)
        assert row["components"] == 1
        assert row["closed_all_bad_components"] == 0
        rows.append({
            "orbit_index": oi,
            "orbit_size": orbit_size,
            "multiplicity_vector": list(counts),
            **row,
        })

    print(json.dumps({
        "scope":
            "exact binary rank-4 n=10 two-deletion-robust represented multisets",
        "gl4_2_orbits": len(reps),
        "four_block_patterns": [list(p) for p in FOUR_BLOCK_PATTERNS],
        "all_state_graphs_connected": True,
        "orbits_with_closed_all_bad_component": 0,
        "rows": rows,
        "interpretation": (
            "The closed all-bad components surviving adjacent swaps, point "
            "pivots, and even arbitrary single transpositions disappear once "
            "two canonical consecutive four-position 2+2-scale repairs are "
            "allowed. Every exact orbit representative becomes connected."
        ),
        "claim_level": "exact finite computation; not Lean certification",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
