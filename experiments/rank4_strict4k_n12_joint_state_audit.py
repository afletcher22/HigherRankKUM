#!/usr/bin/env python3
"""Exact joint-state audit for one hard binary strict n=12 representative.

Representative projective multiplicities:
    (2,2,1,1,1,1,0,1,1,1,0,1,0,0,0)
with strict-density profile (m1,m2,m3)=(2,5,8).

States are pairs (e,sigma), where e is the omitted labelled element and sigma
is a deletion CBO of M\e, modulo rotation via the least remaining label.

Moves:
  * cyclic adjacent swaps preserving the deletion CBO;
  * omitted-element pivots: replace one ordered entry f by e and make f the
    new omitted element, provided the resulting deletion order is a CBO.

Success means the blocker word contains at least four consecutive nonblockers,
equivalently e can be inserted at some gap.

The script also audits the fixed-e adjacent-swap graph for e=0 to show why
omitted-element pivots are genuinely necessary.

Exact finite computation; not Lean certification.
"""

from __future__ import annotations

import json
from collections import Counter, deque
from functools import lru_cache

CONFIG = (2,2,1,1,1,1,0,1,1,1,0,1,0,0,0)
N = 12


def rank2(values):
    piv = [0] * 4
    r = 0
    for value in values:
        x = value
        while x:
            p = x.bit_length() - 1
            if piv[p]:
                x ^= piv[p]
            else:
                piv[p] = x
                r += 1
                break
    return r


VALUES = tuple(
    point
    for point, multiplicity in enumerate(CONFIG, start=1)
    for _ in range(multiplicity)
)
assert len(VALUES) == N


def enumerate_cbos(omitted):
    labels = tuple(i for i in range(N) if i != omitted)
    first = labels[0]
    path = [first]
    out = []
    m = len(labels)

    @lru_cache(None)
    def basis4(labels4):
        return rank2(VALUES[i] for i in labels4) == 4

    def dfs(rem):
        if not rem:
            order = tuple(path)
            if all(
                basis4(tuple(order[(i + j) % m] for j in range(4)))
                for i in range(m - 3, m)
            ):
                out.append(order)
            return
        for x in rem:
            if len(path) >= 3 and not basis4(tuple(path[-3:] + [x])):
                continue
            path.append(x)
            dfs(tuple(y for y in rem if y != x))
            path.pop()

    dfs(tuple(x for x in labels if x != first))
    return tuple(out)


def blocker_word(omitted, order):
    m = len(order)
    out = []
    for i in range(m):
        triple = tuple(order[(i + j) % m] for j in range(3))
        r = rank2(VALUES[x] for x in triple)
        out.append(
            rank2([*(VALUES[x] for x in triple), VALUES[omitted]]) == r
        )
    return tuple(out)


def zero_runs(bits):
    m = len(bits)
    if all(not b for b in bits):
        return [m]
    if all(bits):
        return []
    start = next(i for i, b in enumerate(bits) if b)
    runs = []
    run = 0
    for t in range(1, m + 1):
        b = bits[(start + t) % m]
        if not b:
            run += 1
        elif run:
            runs.append(run)
            run = 0
    if run:
        runs.append(run)
    return runs


def successful(state):
    e, order = state
    runs = zero_runs(blocker_word(e, order))
    return bool(runs) and max(runs) >= 4


def canonical(order, omitted):
    first = next(i for i in range(N) if i != omitted)
    j = order.index(first)
    return order[j:] + order[:j]


def main():
    by_e = {e: enumerate_cbos(e) for e in range(N)}
    cbo_counts = [len(by_e[e]) for e in range(N)]

    joint = {
        (e, order)
        for e in range(N)
        for order in by_e[e]
    }
    success = {s for s in joint if successful(s)}

    def adjacent_neighbors(state):
        e, order = state
        m = len(order)
        for i in range(m):
            a = list(order)
            j = (i + 1) % m
            a[i], a[j] = a[j], a[i]
            t = (e, canonical(tuple(a), e))
            if t in joint:
                yield t

    def pivot_neighbors(state):
        e, order = state
        for i, f in enumerate(order):
            a = list(order)
            a[i] = e
            t = (f, canonical(tuple(a), f))
            if t in joint:
                yield t

    def joint_neighbors(state):
        yield from adjacent_neighbors(state)
        yield from pivot_neighbors(state)

    # Fixed-e=0 adjacent-swap audit.
    fixed = {(0, o) for o in by_e[0]}
    fixed_success = fixed & success
    fixed_adj = {
        s: set(adjacent_neighbors(s))
        for s in fixed
    }

    unseen = set(fixed)
    fixed_components = []
    while unseen:
        root = next(iter(unseen))
        unseen.remove(root)
        comp = {root}
        q = [root]
        while q:
            u = q.pop()
            for v in fixed_adj[u]:
                if v in unseen:
                    unseen.remove(v)
                    comp.add(v)
                    q.append(v)
        fixed_components.append(comp)

    fixed_component_hist = Counter(
        (len(comp), bool(comp & fixed_success))
        for comp in fixed_components
    )
    closed_bad = [c for c in fixed_components if not (c & fixed_success)]

    fixed_dist = {s: 0 for s in fixed_success}
    q = deque(fixed_success)
    while q:
        u = q.popleft()
        for v in fixed_adj[u]:
            if v not in fixed_dist:
                fixed_dist[v] = fixed_dist[u] + 1
                q.append(v)

    # Full joint graph: all moves are reversible, so BFS from success exactly
    # detects closed all-bad components and gives distance to success.
    joint_dist = {s: 0 for s in success}
    q = deque(success)
    while q:
        u = q.popleft()
        for v in joint_neighbors(u):
            if v not in joint_dist:
                joint_dist[v] = joint_dist[u] + 1
                q.append(v)

    # Connectivity from one arbitrary state.
    root = next(iter(joint))
    seen = {root}
    q = deque([root])
    while q:
        u = q.popleft()
        for v in joint_neighbors(u):
            if v not in seen:
                seen.add(v)
                q.append(v)

    # Exact edge counts.
    adjacent_directed = 0
    pivot_directed = 0
    for s in joint:
        adjacent_directed += sum(1 for _ in adjacent_neighbors(s))
        pivot_directed += sum(1 for _ in pivot_neighbors(s))
    assert adjacent_directed % 2 == 0
    assert pivot_directed % 2 == 0

    out = {
        "scope": "exact fixed binary strict n=12 representative",
        "projective_multiplicities": list(CONFIG),
        "labelled_values": list(VALUES),
        "strict_profile": [2,5,8],
        "cbo_counts_by_omitted_label": cbo_counts,
        "joint_graph": {
            "states": len(joint),
            "successful_states": len(success),
            "adjacent_swap_edges": adjacent_directed // 2,
            "omitted_element_pivot_edges": pivot_directed // 2,
            "total_edges": (adjacent_directed + pivot_directed) // 2,
            "connected": len(seen) == len(joint),
            "closed_all_bad_states": len(joint) - len(joint_dist),
            "max_distance_to_success": max(joint_dist.values()),
            "distance_distribution": {
                str(k): v for k, v in sorted(Counter(joint_dist.values()).items())
            },
        },
        "fixed_e0_adjacent_only": {
            "states": len(fixed),
            "successful_states": len(fixed_success),
            "components": len(fixed_components),
            "component_class_histogram": {
                str(k): v for k, v in sorted(fixed_component_hist.items())
            },
            "closed_all_bad_components": len(closed_bad),
            "closed_all_bad_states": sum(len(c) for c in closed_bad),
            "reachable_max_distance_to_success": max(fixed_dist.values()),
        },
        "interpretation": (
            "Adjacent swaps alone leave many closed all-bad components for a "
            "fixed omitted element, but adding omitted-element pivots makes the "
            "entire 97,072-state graph connected and puts every state within "
            "five moves of a successful state."
        ),
        "claim_level": "exact finite computation; not Lean certification",
    }

    assert out["joint_graph"]["states"] == 97072
    assert out["joint_graph"]["successful_states"] == 27952
    assert out["joint_graph"]["adjacent_swap_edges"] == 136064
    assert out["joint_graph"]["omitted_element_pivot_edges"] == 120864
    assert out["joint_graph"]["total_edges"] == 256928
    assert out["joint_graph"]["connected"]
    assert out["joint_graph"]["closed_all_bad_states"] == 0
    assert out["joint_graph"]["max_distance_to_success"] == 5
    assert out["fixed_e0_adjacent_only"]["states"] == 14592
    assert out["fixed_e0_adjacent_only"]["successful_states"] == 3272
    assert out["fixed_e0_adjacent_only"]["closed_all_bad_components"] == 232
    assert out["fixed_e0_adjacent_only"]["closed_all_bad_states"] == 368

    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
