#!/usr/bin/env python3
"""Exhaustive joint-state audit for all qualifying simple binary rank-4 n=8 matroids.

The ground representation is every 8-point subset of PG(3,2), identified
with the 15 nonzero vectors of GF(2)^4 encoded as integers 1..15.

Qualification is exact universal single-deletion stability. In the simple
binary n=8 case the rank-1 and rank-2 slack inequalities are automatic, and
the rank-3 condition is equivalent to every projective hyperplane containing
at most five chosen points.

For each qualifying matroid, build the complete (e,sigma) graph under:
  * cyclic adjacent swaps preserving the deletion CBO;
  * point pivots preserving the new deletion CBO.

Then test:
  * presence of closed all-bad connected components;
  * failure of lexicographically nondecreasing nonblocker-run-profile escape;
  * minimum Lmax valley depth needed to reach a successful state.

This is exact finite computation, not Lean certification.
"""

import collections
import itertools
import json

from rank4_joint_state_profile_audit import graph, components, profile


def parity_dot(a: int, b: int) -> int:
    return ((a & b).bit_count() & 1)


def qualifying(M) -> bool:
    max_hyperplane = max(
        sum(parity_dot(h, x) == 0 for x in M)
        for h in range(1, 16)
    )
    return max_hyperplane <= 5


def metrics(vals):
    states, adj = graph(list(vals))
    prof = {s: profile(list(vals), s) for s in states}
    lmax = {s: (prof[s][0] if prof[s] else 0) for s in states}
    success = {s for s in states if lmax[s] >= 4}

    comps = []
    unseen = set(states)
    while unseen:
        root = next(iter(unseen))
        unseen.remove(root)
        stack = [root]
        comp = []
        while stack:
            u = stack.pop()
            comp.append(u)
            for v in adj[u]:
                if v in unseen:
                    unseen.remove(v)
                    stack.append(v)
        comps.append(comp)

    all_bad_components = sum(
        1 for comp in comps if all(s not in success for s in comp)
    )

    # Lexicographically nondecreasing run-profile reachability.
    rev = {s: [] for s in states}
    for u in states:
        for v in adj[u]:
            if prof[v] >= prof[u]:
                rev[v].append(u)
    reach = set(success)
    stack = list(success)
    while stack:
        v = stack.pop()
        for u in rev[v]:
            if u not in reach:
                reach.add(u)
                stack.append(u)
    no_monotone_escape = sum(1 for s in states if s not in reach)

    # Minimal Lmax drop, computed from threshold subgraphs.
    worst_drop = 0
    for L in (1, 2, 3):
        starts = [s for s in states if lmax[s] == L and s not in success]
        if not starts:
            continue
        needed = {s: None for s in starts}
        for d in range(L + 1):
            threshold = L - d
            allowed = {s for s in states if lmax[s] >= threshold}
            unseen = set(allowed)
            good = set()
            while unseen:
                root = next(iter(unseen))
                unseen.remove(root)
                stack = [root]
                comp = []
                has_success = False
                while stack:
                    u = stack.pop()
                    comp.append(u)
                    if u in success:
                        has_success = True
                    for v in adj[u]:
                        if v in unseen:
                            unseen.remove(v)
                            stack.append(v)
                if has_success:
                    good.update(comp)
            for s in starts:
                if needed[s] is None and s in good:
                    needed[s] = d
            if all(v is not None for v in needed.values()):
                break
        if any(v is None for v in needed.values()):
            worst_drop = 99
        else:
            worst_drop = max(worst_drop, max(needed.values(), default=0))

    return (
        len(states),
        len(comps),
        all_bad_components,
        no_monotone_escape,
        worst_drop,
    )


def main():
    counts = collections.Counter()
    qualifying_count = 0
    for M in itertools.combinations(range(1, 16), 8):
        if not qualifying(M):
            continue
        qualifying_count += 1
        counts[metrics(M)] += 1

    out = {
        "qualifying_matroids": qualifying_count,
        "metric_tuple_definition": [
            "states",
            "components",
            "closed_all_bad_components",
            "states_without_lexicographically_nondecreasing_profile_escape",
            "maximum_required_Lmax_drop",
        ],
        "classes": {
            str(k): v for k, v in sorted(counts.items())
        },
        "closed_all_bad_component_matroids": sum(
            v for k, v in counts.items() if k[2] != 0
        ),
        "maximum_required_Lmax_drop": max(k[4] for k in counts),
        "representatives": {
            "valley": [7, 8, 10, 11, 12, 13, 14, 15],
            "all_states_isolated_successful": [1, 3, 4, 6, 8, 10, 13, 15],
        },
        "claim_level": "exact finite computation; not Lean certification",
    }
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
