#!/usr/bin/env python3
"""Seeded fixed-e four-block stress on dense rank-4 sparse-paving matroids at n=14.

For each seed 1000,...,1009:
  * greedily build a maximal family H of 4-subsets of [14] with pairwise
    intersections at most 2; this specifies a rank-4 sparse-paving matroid
    whose circuit-hyperplanes are H;
  * sample deletion CBOs for random omitted elements;
  * retain bad states, i.e. deletion CBOs with no insertion gap for e;
  * search fixed-e four-block moves, allowing every permutation of four
    cyclically consecutive positions that preserves the deletion CBO.

The sample is deliberately nonrepresentable-style; no representability is
assumed or tested.

Finite seeded computation only; not Lean certification and not exhaustive over
all sparse-paving matroids.
"""

from collections import deque
from itertools import combinations, permutations
import json
import random

ALL4 = tuple(p for p in permutations(range(4)) if p != (0,1,2,3))


def greedy_sparse_paving(n, seed):
    rng = random.Random(seed)
    blocks = list(combinations(range(n), 4))
    rng.shuffle(blocks)
    H = []
    for B in blocks:
        S = set(B)
        if all(len(S.intersection(C)) <= 2 for C in H):
            H.append(frozenset(B))
    return frozenset(H)


def canonical(order):
    order = tuple(order)
    i = order.index(min(order))
    return order[i:] + order[:i]


def cbo(order, H):
    m = len(order)
    return all(
        frozenset(order[(i+j) % m] for j in range(4)) not in H
        for i in range(m)
    )


def successful(order, e, H):
    for gap in range(len(order)):
        full = list(order)
        full.insert(gap, e)
        if cbo(full, H):
            return True
    return False


def random_cbo(n, e, H, rng, tries=20):
    labels = [x for x in range(n) if x != e]
    for _ in range(tries):
        rng.shuffle(labels)
        order = canonical(labels)
        if cbo(order, H):
            return order
    return None


def neighbors(order, H):
    order = tuple(order)
    m = len(order)
    out = set()
    for start in range(m):
        inds = [(start+j) % m for j in range(4)]
        vals = [order[i] for i in inds]
        for patt in ALL4:
            a = list(order)
            for dst, src in enumerate(patt):
                a[inds[dst]] = vals[src]
            t = canonical(a)
            if t != order and cbo(t, H):
                out.add(t)
    return out


def distance_to_success(order, e, H, maxdepth=4, maxnodes=50000):
    if successful(order, e, H):
        return 0
    seen = {order}
    q = deque([(order, 0)])
    while q and len(seen) < maxnodes:
        u, d = q.popleft()
        if d >= maxdepth:
            continue
        for v in neighbors(u, H):
            if v in seen:
                continue
            if successful(v, e, H):
                return d + 1
            seen.add(v)
            q.append((v, d+1))
    return None


def main():
    rows = []
    total_bad = 0
    for idx in range(10):
        hseed = 1000 + idx
        H = greedy_sparse_paving(14, hseed)
        rng = random.Random(2000 + idx)
        bad = []
        attempts = 0
        while len(bad) < 10 and attempts < 5000:
            attempts += 1
            e = rng.randrange(14)
            order = random_cbo(14, e, H, rng)
            if order is not None and not successful(order, e, H):
                state = (e, order)
                if state not in bad:
                    bad.append(state)

        distances = [distance_to_success(o, e, H) for e, o in bad]
        assert all(d == 1 for d in distances)
        total_bad += len(bad)
        rows.append({
            "hyperplane_seed": hseed,
            "circuit_hyperplanes": len(H),
            "bad_states_found": len(bad),
            "sampling_attempts": attempts,
            "distance_histogram": {"1": len(bad)},
        })

    assert total_bad == 71
    print(json.dumps({
        "scope": "dense greedy rank-4 sparse-paving matroids on n=14",
        "matroids": 10,
        "circuit_hyperplane_range": [62, 68],
        "bad_states": total_bad,
        "moves": (
            "arbitrary CBO-preserving permutations of four consecutive "
            "positions; omitted element fixed; no pivots"
        ),
        "distance_histogram": {"1": total_bad},
        "rows": rows,
        "interpretation": (
            "All 71 sampled bad states became favorable after one fixed-e "
            "four-block reorder. This provides nonrepresentable-style stress "
            "for the t=0 fixed-e component conjecture."
        ),
        "claim_level": (
            "seeded finite computation; not exhaustive and not Lean certified"
        )
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
