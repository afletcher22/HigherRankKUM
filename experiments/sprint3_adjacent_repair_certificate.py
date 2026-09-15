#!/usr/bin/env python3
"""Exact adjacent re-pairing audit for ONE labelled ten-element matroid.

No random sampling and no claim about all rank-four matroids. Enumerates all
22,680 cyclic pair decompositions of the Sprint 2 witness, modulo rotation
and internal pair orientation (reflection is retained). Distinct labels with
equal vector values remain distinct elements throughout.

Run from the repository root:
    python3 experiments/sprint3_adjacent_repair_certificate.py
"""

import json
from collections import deque
from itertools import combinations, permutations, product

from sprint2_pair_obstruction_certificate import (
    ELEMENTS, rank_gf2, rank_by_span, verify_density,
)

N, H = 5, 2
LABELS = tuple(range(2 * N))
INITIAL = tuple((i, i + 1) for i in range(0, 2 * N, 2))


def mask(labels):
    labels = tuple(labels)
    assert len(set(labels)) == len(labels)
    return sum(1 << x for x in labels)


BASES = {
    mask(c) for c in combinations(LABELS, 2 * H)
    if rank_gf2(ELEMENTS[x] for x in c) == 2 * H
}


def canonical(state):
    state = tuple(tuple(sorted(p)) for p in state)
    assert sorted(x for p in state for x in p) == list(LABELS)
    return min(state[i:] + state[:i] for i in range(N))


def aligned(state, i):
    return tuple(x for j in range(H) for x in state[(i + j) % N])


def admissible(state):
    return all(mask(aligned(state, i)) in BASES for i in range(N))


def relations(state):
    return tuple(
        tuple(tuple(
            mask((state[i][1 - a],)
                 + tuple(x for j in range(1, H) for x in state[(i + j) % N])
                 + (state[(i + H) % N][b],)) in BASES
            for b in (0, 1)) for a in (0, 1))
        for i in range(N)
    )


def flatten(state, bits):
    return tuple(x for p, bit in zip(state, bits) for x in (p[bit], p[1 - bit]))


def direct_cbo(labels):
    assert sorted(labels) == list(LABELS)
    return all(rank_by_span(ELEMENTS[labels[(i + j) % (2 * N)]]
                            for j in range(2 * H)) == 2 * H
               for i in range(2 * N))


def orientation(state):
    rr = relations(state)
    assert all(all(any(row) for row in rel)
               and all(any(rel[a][b] for a in (0, 1)) for b in (0, 1))
               for rel in rr)
    answer = next((bits for bits in product((0, 1), repeat=N)
                   if all(rr[i][bits[i]][bits[(i + H) % N]] for i in range(N))), None)
    forced = all(sum(map(sum, rel)) == 2 for rel in rr)
    parity = sum(rel[0][1] for rel in rr) % 2 if forced else None
    assert (answer is None) == (forced and parity == 1)
    if answer is not None:
        assert direct_cbo(flatten(state, answer))
    return answer


def candidate_moves(state):
    """Exchange one labelled element between neighboring pairs; four per edge."""
    for i in range(N):
        j = (i + 1) % N
        for a, b in product((0, 1), repeat=2):
            new = list(state)
            left, right = list(state[i]), list(state[j])
            left[a], right[b] = right[b], left[a]
            new[i], new[j] = tuple(left), tuple(right)
            new = tuple(new)
            # Only the window ending at i and the window starting at i+1
            # can change their element sets. Check the proposed general
            # boundary criterion against all windows in this finite case.
            boundary_ok = all(mask(aligned(new, k)) in BASES
                              for k in ((i - H + 1) % N, j))
            assert boundary_ok == admissible(new)
            yield (i, a, b), canonical(new), boundary_ok


def all_pair_cycles():
    # Fix the pair containing label 0 first to quotient by cyclic rotation.
    for partner in LABELS[1:]:
        rest = tuple(x for x in LABELS[1:] if x != partner)
        for perm in permutations(rest):
            if any(perm[j] > perm[j + 1] for j in range(0, 2 * N - 2, 2)):
                continue
            yield ((0, partner),) + tuple(zip(perm[::2], perm[1::2]))


def main():
    verify_density()
    total = 0
    states = {}
    for state in all_pair_cycles():
        total += 1
        if admissible(state):
            assert state not in states
            states[state] = orientation(state)
    assert total == 22680
    assert len(states) == 576
    bad = {s for s, bits in states.items() if bits is None}
    assert len(bad) == 8

    graph = {}
    for state in states:
        graph[state] = {new for _, new, ok in candidate_moves(state) if ok}
        assert graph[state] <= states.keys()
    assert all(state in graph[new] for state in states for new in graph[state])
    stuck = {s for s in bad if all(states[t] is None for t in graph[s])}
    assert not stuck

    components = []
    remaining = set(states)
    while remaining:
        seed = min(remaining)
        queue, component = deque([seed]), {seed}
        while queue:
            for new in graph[queue.popleft()]:
                if new not in component:
                    component.add(new)
                    queue.append(new)
        remaining -= component
        components.append({"vertices": len(component), "unorientable": len(component & bad)})

    successful = [(move, new) for move, new, ok in candidate_moves(INITIAL)
                  if ok and states[new] is not None]
    assert len(successful) == len(graph[INITIAL]) == 6
    move, repaired = successful[0]
    bits = states[repaired]
    order = flatten(repaired, bits)
    assert direct_cbo(order)
    print(json.dumps({
        "scope": "all cyclic pair partitions of this one labelled binary rank-four matroid",
        "vectors_by_label": ELEMENTS,
        "pair_cycles_examined": total,
        "admissible_pair_cycles": len(states),
        "unorientable_pair_cycles": len(bad),
        "unorientable_without_single_adjacent_repair": len(stuck),
        "directed_admissible_moves": sum(map(len, graph.values())),
        "components": components,
        "original_admissible_neighbors": len(graph[INITIAL]),
        "repair": {"exchange": move, "pairs_by_label": repaired,
                   "orientations": bits, "local_relations": relations(repaired),
                   "cbo_labels": order, "cbo_vectors": [ELEMENTS[x] for x in order]},
        "boundary_criterion_checks": len(states) * N * 4,
        "status": "exact finite computational certificate; not a universal repair theorem",
    }, indent=2))


if __name__ == "__main__":
    main()
