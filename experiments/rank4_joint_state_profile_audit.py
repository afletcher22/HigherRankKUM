#!/usr/bin/env python3
"""Joint-state run-profile audit for two exact rank-4 witnesses.

Moves:
  * cyclic adjacent swaps preserving the deletion CBO;
  * point pivots replacing an entry f by the omitted e, when the resulting
    order is a CBO of M\f.

The run profile is the descending tuple of cyclic nonblocker-run lengths.
Success means first entry >= 4.

This exhaustively reproduces the known 432-state strict8 and 4224-state
t0-n10 state graphs, then tests whether every unsuccessful state can reach
success along edges with nondecreasing run profile.
"""

import collections
import json


def rank2(vals):
    basis = [0] * 4
    r = 0
    for x in vals:
        y = x
        while y:
            i = y.bit_length() - 1
            if basis[i]:
                y ^= basis[i]
            else:
                basis[i] = y
                r += 1
                break
    return r


def cbo(order, vals):
    m = len(order)
    return all(rank2([vals[order[(i+j) % m]] for j in range(4)]) == 4
               for i in range(m))


def canonical(order):
    order = tuple(order)
    m = min(order)
    i = order.index(m)
    return order[i:] + order[:i]


def deletion_cbos(vals, e):
    labels = [i for i in range(len(vals)) if i != e]
    first = min(labels)
    path = [first]
    out = []

    def dfs(rem):
        if not rem:
            o = tuple(path)
            if cbo(o, vals):
                out.append(o)
            return
        for x in rem:
            if len(path) >= 3 and rank2([vals[i] for i in path[-3:] + [x]]) < 4:
                continue
            path.append(x)
            dfs([y for y in rem if y != x])
            path.pop()

    dfs([i for i in labels if i != first])
    return out


def blocker_word(vals, e, order):
    m = len(order)
    out = []
    for i in range(m):
        tri = [order[(i+j) % m] for j in range(3)]
        r = rank2([vals[x] for x in tri])
        out.append(rank2([vals[x] for x in tri] + [vals[e]]) == r)
    return tuple(out)


def zero_runs(bs):
    m = len(bs)
    if all(not b for b in bs):
        return [m]
    if all(bs):
        return []
    start = next(i for i, b in enumerate(bs) if b)
    runs = []
    run = 0
    for t in range(1, m + 1):
        b = bs[(start + t) % m]
        if not b:
            run += 1
        elif run:
            runs.append(run)
            run = 0
    if run:
        runs.append(run)
    return runs


def profile(vals, state):
    e, order = state
    return tuple(sorted(zero_runs(blocker_word(vals, e, order)), reverse=True))


def graph(vals):
    states = []
    state_set = set()
    for e in range(len(vals)):
        for o in deletion_cbos(vals, e):
            s = (e, o)
            states.append(s)
            state_set.add(s)

    adj = {s: set() for s in states}
    for e, o in states:
        s = (e, o)
        m = len(o)
        for i in range(m):
            a = list(o)
            j = (i + 1) % m
            a[i], a[j] = a[j], a[i]
            t = (e, canonical(a))
            if t in state_set:
                adj[s].add(t)
        for i, f in enumerate(o):
            a = list(o)
            a[i] = e
            t = (f, canonical(a))
            if t in state_set:
                adj[s].add(t)
    return states, adj


def components(states, adj):
    unseen = set(states)
    sizes = []
    while unseen:
        root = next(iter(unseen))
        unseen.remove(root)
        stack = [root]
        size = 0
        while stack:
            u = stack.pop()
            size += 1
            for v in adj[u]:
                if v in unseen:
                    unseen.remove(v)
                    stack.append(v)
        sizes.append(size)
    return sorted(sizes, reverse=True)


def audit(vals):
    states, adj = graph(vals)
    prof = {s: profile(vals, s) for s in states}
    success = {s for s in states if prof[s] and prof[s][0] >= 4}

    # Directed edge u->v is allowed only if profile(v) >= profile(u).
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

    local_max = [
        s for s in states
        if s not in success and all(prof[v] <= prof[s] for v in adj[s])
    ]
    bad = [s for s in states if s not in reach]

    witness = None
    if bad:
        s = bad[0]
        witness = {
            "omitted_label": s[0],
            "order": list(s[1]),
            "profile": list(prof[s]),
            "blockers": [int(x) for x in blocker_word(vals, *s)],
            "neighbor_profiles": sorted([list(prof[v]) for v in adj[s]]),
        }

    return {
        "states": len(states),
        "undirected_edges": sum(len(x) for x in adj.values()) // 2,
        "components": components(states, adj),
        "successful_states": len(success),
        "states_without_nondecreasing_profile_escape": len(bad),
        "unsuccessful_local_profile_maxima": len(local_max),
        "bad_profile_counts": {
            str(k): v for k, v in collections.Counter(prof[s] for s in bad).items()
        },
        "witness_local_maximum": witness,
    }


def main():
    out = {
        "strict8": audit([7, 8, 10, 11, 12, 13, 14, 15]),
        "t0_n10": audit([2, 4, 9, 10, 10, 11, 12, 12, 13, 15]),
        "interpretation": (
            "Lexicographically nondecreasing nonblocker-run profile is not a "
            "universal escape potential: strict8 has genuine bad local maxima. "
            "The t0 n=10 witness nevertheless has monotone escape from every state."
        ),
    }
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
