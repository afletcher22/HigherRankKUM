#!/usr/bin/env python3
"""Sparse-paving n=10 stress test for prescribed-element lifting.

A rank-4 sparse-paving matroid on ten labelled elements is specified by a
family H of 4-element circuit-hyperplanes with pairwise intersection at most 2.
All other 4-subsets are bases.

This certificate checks:
  * the explicit 30-block Steiner quadruple system SQS(10), which is extremal;
  * 1000 deterministic dense random stable families, built by repeated greedy
    packing of 4-subsets.

For every matroid and every omitted label e, it searches for a CBO of M\e
into which e can be inserted, and directly verifies all cyclic 4-windows of
the resulting order are bases.

Finite computation only; not Lean certification.
"""

from __future__ import annotations

import itertools
import json
import random
from collections import Counter

E = tuple(range(10))
ALL4 = tuple(itertools.combinations(E, 4))


def is_base(S, H):
    return frozenset(S) not in H


def cyclic_cbo(order, H):
    m = len(order)
    return all(
        is_base([order[(i + j) % m] for j in range(4)], H)
        for i in range(m)
    )


def find_favorable(H, omitted):
    arr = [x for x in E if x != omitted]
    m = len(arr)
    path = [arr[0]]
    remaining = tuple(arr[1:])
    nodes = 0

    def dfs(rem):
        nonlocal nodes
        nodes += 1
        if not rem:
            order = tuple(path)
            if not cyclic_cbo(order, H):
                return None
            for gap in range(m):
                full = list(order)
                full.insert(gap, omitted)
                if cyclic_cbo(tuple(full), H):
                    return {
                        "deletion_order": list(order),
                        "gap": gap,
                        "nodes": nodes,
                    }
            return None

        for x in rem:
            if len(path) >= 3 and not is_base(path[-3:] + [x], H):
                continue
            path.append(x)
            ans = dfs(tuple(y for y in rem if y != x))
            if ans is not None:
                return ans
            path.pop()
        return None

    return dfs(remaining), nodes


def stable(H):
    H = list(H)
    return all(
        len(H[i] & H[j]) <= 2
        for i in range(len(H))
        for j in range(i)
    )


def sqs10():
    # Standard cyclic presentation on Z_10:
    # {i,i+1,i+3,i+4}, {i,i+1,i+2,i+6}, {i,i+2,i+4,i+7}.
    blocks = set()
    for i in range(10):
        blocks.add(frozenset((i, (i + 1) % 10, (i + 3) % 10, (i + 4) % 10)))
        blocks.add(frozenset((i, (i + 1) % 10, (i + 2) % 10, (i + 6) % 10)))
        blocks.add(frozenset((i, (i + 2) % 10, (i + 4) % 10, (i + 7) % 10)))
    assert len(blocks) == 30
    assert stable(blocks)
    triples = Counter(
        T
        for B in blocks
        for T in itertools.combinations(sorted(B), 3)
    )
    assert len(triples) == 120
    assert set(triples.values()) == {1}
    return frozenset(blocks)


def greedy_stable(seed, trials=10):
    rng = random.Random(seed)
    best = frozenset()
    for _ in range(trials):
        order = list(ALL4)
        rng.shuffle(order)
        H = []
        for Q in order:
            B = frozenset(Q)
            if all(len(B & C) <= 2 for C in H):
                H.append(B)
        if len(H) > len(best):
            best = frozenset(H)
    assert stable(best)
    return best


def audit(H):
    failures = []
    max_nodes = 0
    for e in E:
        witness, nodes = find_favorable(H, e)
        max_nodes = max(max_nodes, nodes)
        if witness is None:
            failures.append(e)
    return failures, max_nodes


def main():
    extremal = sqs10()
    sqs_failures, sqs_max_nodes = audit(extremal)
    assert sqs_failures == []

    size_hist = Counter()
    random_failure = None
    random_max_nodes = 0
    for j in range(1000):
        H = greedy_stable(100000 + j, trials=10)
        size_hist[len(H)] += 1
        failures, max_nodes = audit(H)
        random_max_nodes = max(random_max_nodes, max_nodes)
        if failures:
            random_failure = {
                "seed": 100000 + j,
                "circuit_hyperplanes": len(H),
                "bad_elements": failures,
            }
            break

    assert random_failure is None

    out = {
        "scope": "rank-4 sparse-paving matroids on 10 labelled elements",
        "extremal_sqs10": {
            "circuit_hyperplanes": len(extremal),
            "bad_prescribed_elements": 0,
            "max_search_nodes": sqs_max_nodes,
        },
        "dense_random": {
            "samples": 1000,
            "greedy_trials_per_sample": 10,
            "circuit_hyperplane_count_histogram": dict(sorted(size_hist.items())),
            "bad_matroids": 0,
            "max_search_nodes": random_max_nodes,
        },
        "interpretation": (
            "No prescribed-element lifting failure was found. The 30-block "
            "SQS(10) is the extremal stable circuit-hyperplane family; the "
            "random sample stresses many dense non-coordinate sparse-paving systems."
        ),
        "claim_level": "finite computation; SQS case exact, random family seeded",
    }
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
