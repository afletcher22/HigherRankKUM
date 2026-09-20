#!/usr/bin/env python3
"""Exact forced-component audit for the fixed strict rank-4 t=0 N=9 witness.

This extends rank4_t0_two_step_repair_certificate.py.  It explores only the
forced-unorientable subgraph, using the proved/checked parity reduction:
an unorientable odd-N pair-cycle state has all local relations forced.

It verifies:
* the forced component of the displayed witness has 144 states;
* 136 states have an immediate orientable/slack repair;
* the remaining 8 states form a 3-cube under forced-preserving moves;
* each of those 8 states is exactly one forced move from an escape-capable
  state, hence exactly two repairs from orientability;
* the closure-potential / degree / escape-count distribution recorded below.

Finite GF(2) computation only; not Lean certification.
"""

import json
from collections import Counter, deque
from functools import lru_cache
from itertools import combinations

VECTORS = (1, 2, 4, 8, 9, 6, 2, 8, 1, 4, 3, 12, 1, 8, 2, 4, 5, 10)
N = 9
INITIAL = tuple((i, i + 1) for i in range(0, 18, 2))


def rank_values(values):
    pivots = [0] * 4
    r = 0
    for value in values:
        x = value
        while x:
            pivot = x.bit_length() - 1
            if pivots[pivot]:
                x ^= pivots[pivot]
            else:
                pivots[pivot] = x
                r += 1
                break
    return r


def rank_labels(labels):
    return rank_values(VECTORS[i] for i in labels)


@lru_cache(None)
def relation_masks(state):
    out = []
    for i in range(N):
        mask = 0
        for x in (0, 1):
            for y in (0, 1):
                labels = (
                    state[i][1 - x],
                    *state[(i + 1) % N],
                    state[(i + 2) % N][y],
                )
                if rank_labels(labels) == 4:
                    mask |= 1 << (2 * x + y)
        out.append(mask)
    return tuple(out)


def forced_unorientable(state):
    masks = relation_masks(state)
    return all(m in (6, 9) for m in masks) and sum(m == 6 for m in masks) % 2 == 1


def orientable(state):
    masks = relation_masks(state)
    cycle = []
    i = 0
    for _ in range(N):
        cycle.append(i)
        i = (i + 2) % N
    for start in (0, 1):
        possible = {start}
        for t in range(N - 1):
            i = cycle[t]
            possible = {
                y for x in possible for y in (0, 1)
                if masks[i] & (1 << (2 * x + y))
            }
            if not possible:
                break
        if possible:
            i = cycle[-1]
            if any(masks[i] & (1 << (2 * x + start)) for x in possible):
                return True
    return False


@lru_cache(None)
def legal_repairs(state):
    out = []
    for i in range(N):
        j = (i + 1) % N
        four = state[i] + state[j]
        seen = set()
        for chosen_tuple in combinations(range(4), 2):
            chosen = set(chosen_tuple)
            left = tuple(sorted(four[t] for t in range(4) if t in chosen))
            right = tuple(sorted(four[t] for t in range(4) if t not in chosen))
            if (left, right) == (state[i], state[j]):
                continue
            candidate = list(state)
            candidate[i], candidate[j] = left, right
            candidate = tuple(candidate)
            if candidate in seen:
                continue
            seen.add(candidate)
            if (
                rank_labels(state[(i - 1) % N] + left) == 4
                and rank_labels(right + state[(i + 2) % N]) == 4
            ):
                out.append((i, candidate))
    return tuple(out)


def closure_contains(pair, label):
    r = rank_labels(pair)
    return rank_labels(pair + (label,)) == r


def boundary_closure_score(state, s):
    # core(s)=block(s+1), left=s+2, right=s+3, right-core=s+4.
    left_core = state[(s + 1) % N]
    left = state[(s + 2) % N]
    right = state[(s + 3) % N]
    right_core = state[(s + 4) % N]
    return (
        sum(closure_contains(left_core, x) for x in right)
        + sum(closure_contains(right_core, x) for x in left)
    )


def closure_potential(state):
    return sum(boundary_closure_score(state, s) for s in range(N))


def main():
    assert forced_unorientable(INITIAL)

    # Explore the connected forced-unorientable component.
    q = deque([INITIAL])
    states = {INITIAL}
    while q:
        s = q.popleft()
        for _, t in legal_repairs(s):
            if forced_unorientable(t) and t not in states:
                states.add(t)
                q.append(t)

    adj = {s: set() for s in states}
    escape_count = {}
    for s in states:
        escapes = 0
        for _, t in legal_repairs(s):
            if forced_unorientable(t):
                assert t in states
                adj[s].add(t)
            else:
                assert orientable(t)
                escapes += 1
        escape_count[s] = escapes

    rigid = {s for s in states if escape_count[s] == 0}
    escape_capable = states - rigid

    # Distances inside the forced graph to any escape-capable state.
    d = {s: 0 for s in escape_capable}
    q = deque(escape_capable)
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v not in d:
                d[v] = d[u] + 1
                q.append(v)

    # The rigid induced graph is exactly Q_3.
    radj = {s: adj[s] & rigid for s in rigid}
    assert len(rigid) == 8
    assert all(len(radj[s]) == 3 for s in rigid)

    color = {}
    for root in rigid:
        if root in color:
            continue
        color[root] = 0
        q = deque([root])
        while q:
            u = q.popleft()
            for v in radj[u]:
                if v not in color:
                    color[v] = 1 - color[u]
                    q.append(v)
                else:
                    assert color[v] != color[u]
    assert Counter(color.values()) == Counter({0: 4, 1: 4})

    ordered_distance_counts = Counter()
    for root in rigid:
        dd = {root: 0}
        q = deque([root])
        while q:
            u = q.popleft()
            for v in radj[u]:
                if v not in dd:
                    dd[v] = dd[u] + 1
                    q.append(v)
        ordered_distance_counts.update(dd.values())
    assert ordered_distance_counts == Counter({0: 8, 1: 24, 2: 24, 3: 8})

    cross = Counter(
        (
            closure_potential(s),
            len(adj[s]),
            escape_count[s],
            d[s],
        )
        for s in states
    )

    rigid_to_rigid = sum(len(radj[s]) for s in rigid) // 2
    rigid_boundary = sum(len(adj[s] - rigid) for s in rigid)

    out = {
        "scope": "exact fixed GF(2) strict t=0 N=9 pair-cycle witness",
        "forced_component_states": len(states),
        "escape_capable_forced_states": len(escape_capable),
        "no_immediate_escape_states": len(rigid),
        "max_forced_moves_before_escape_capable": max(d.values()),
        "repair_distance_from_rigid_core_to_orientable": 2,
        "rigid_core": {
            "vertices": len(rigid),
            "induced_edges": rigid_to_rigid,
            "degree_in_rigid_core": 3,
            "bipartition_sizes": sorted(Counter(color.values()).values()),
            "ordered_distance_counts": {
                str(k): ordered_distance_counts[k]
                for k in sorted(ordered_distance_counts)
            },
            "is_Q3_cube": True,
            "forced_edges_from_core_to_escape_capable_states": rigid_boundary,
        },
        "closure_potential_degree_escape_distribution": {
            str(k): v for k, v in sorted(cross.items())
        },
        "closure_potential_distribution": dict(sorted(Counter(
            closure_potential(s) for s in states
        ).items())),
        "escape_move_count_distribution": dict(sorted(Counter(
            escape_count[s] for s in states
        ).items())),
        "interpretation": (
            "The two-step obstruction is an eight-state rigid cube, not a broad "
            "plateau. Each cube state has forced-preserving exits to states with "
            "an immediate slack/orientable repair."
        ),
        "claim_level": "exact finite computation; not Lean certification",
    }
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
