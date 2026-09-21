#!/usr/bin/env python3
"""Exact simple-binary n=8 four-block state-graph audit.

The 3,375 simple binary rank-4 8-point matroids with universal
single-deletion stability form three GL(4,2) orbits.  For one representative
of each orbit this script constructs the complete state graph (e,sigma), with
moves:

  * any CBO-preserving permutation of four cyclically consecutive entries;
  * any CBO-preserving point pivot.

Because the construction and success predicate are invariant under projective
linear isomorphism, one representative per GL(4,2) orbit is exhaustive.

Finite computation only; not Lean certification.
"""

from collections import deque
from itertools import combinations, permutations
import json

import rank4_joint_state_profile_audit as state_base

POINTS = tuple(range(1, 16))
ALL4 = tuple(p for p in permutations(range(4)) if p != (0,1,2,3))


def rank2(vals):
    piv = [0] * 4
    r = 0
    for value in vals:
        x = value
        while x:
            i = x.bit_length() - 1
            if piv[i]:
                x ^= piv[i]
            else:
                piv[i] = x
                r += 1
                break
    return r


def parity_dot(a, b):
    return (a & b).bit_count() & 1


def qualifying(M):
    return max(
        sum(parity_dot(h, x) == 0 for x in M)
        for h in POINTS
    ) <= 5


def gl_perms():
    out = []
    for imgs in permutations(POINTS, 4):
        if rank2(imgs) != 4:
            continue
        d = {}
        for x in POINTS:
            y = 0
            for bit, img in zip((1,2,4,8), imgs):
                if x & bit:
                    y ^= img
            d[x] = y
        out.append(d)
    assert len(out) == 20160
    return out


def orbit_reps():
    mats = {
        tuple(M)
        for M in combinations(POINTS, 8)
        if qualifying(M)
    }
    assert len(mats) == 3375

    G = gl_perms()
    unseen = set(mats)
    reps = []
    while unseen:
        M = min(unseen)
        orb = {
            tuple(sorted(g[x] for x in M))
            for g in G
        } & mats
        unseen -= orb
        reps.append((M, len(orb)))
    assert sorted(size for _, size in reps) == [15, 840, 2520]
    return reps


def canonical(order):
    order = tuple(order)
    i = order.index(min(order))
    return order[i:] + order[:i]


def successful(vals, state):
    e, order = state
    for gap in range(len(order)):
        full = list(order)
        full.insert(gap, e)
        if state_base.cbo(full, vals):
            return True
    return False


def audit(vals):
    states = set()
    for e in range(8):
        states.update(
            (e, o)
            for o in state_base.deletion_cbos(vals, e)
        )

    good = {s: successful(vals, s) for s in states}
    adj = {s: set() for s in states}

    for e, order in states:
        m = len(order)

        for start in range(m):
            inds = [(start + j) % m for j in range(4)]
            old = [order[i] for i in inds]
            for patt in ALL4:
                a = list(order)
                for dst, src in enumerate(patt):
                    a[inds[dst]] = old[src]
                t = (e, canonical(a))
                if t in states:
                    adj[(e, order)].add(t)
                    adj[t].add((e, order))

        for i, f in enumerate(order):
            a = list(order)
            a[i] = e
            t = (f, canonical(a))
            if t in states:
                adj[(e, order)].add(t)
                adj[t].add((e, order))

    unseen = set(states)
    comps = []
    while unseen:
        root = unseen.pop()
        comp = {root}
        q = [root]
        while q:
            u = q.pop()
            for v in adj[u]:
                if v not in comp:
                    comp.add(v)
                    unseen.discard(v)
                    q.append(v)
        comps.append(comp)

    # Exact shortest distance to success.
    dist = {s: 0 for s in states if good[s]}
    q = deque(dist)
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v not in dist:
                dist[v] = dist[u] + 1
                q.append(v)

    return {
        "states": len(states),
        "successful_states": sum(good.values()),
        "components": len(comps),
        "closed_all_bad_components": sum(
            not any(good[s] for s in comp)
            for comp in comps
        ),
        "component_sizes": sorted((len(c) for c in comps), reverse=True),
        "maximum_distance_to_success":
            max(dist.values()) if len(dist) == len(states) else None,
    }


def main():
    rows = []
    for M, orbit_size in orbit_reps():
        row = audit(list(M))
        assert row["closed_all_bad_components"] == 0
        rows.append({
            "representative": list(M),
            "orbit_size": orbit_size,
            **row,
        })

    out = {
        "scope": (
            "all simple binary rank-4 n=8 matroids with universal "
            "single-deletion stability"
        ),
        "qualifying_matroids": 3375,
        "gl4_2_orbits": 3,
        "rows": rows,
        "orbits_with_closed_all_bad_component": 0,
        "maximum_distance_to_success":
            max(r["maximum_distance_to_success"] for r in rows),
        "interpretation": (
            "The arbitrary-four-block-plus-pivot graph has no closed all-bad "
            "component in any of the three exact GL(4,2) orbits.  The hardest "
            "orbit has repair radius two."
        ),
        "claim_level": "exact finite computation; not Lean certification",
    }
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
