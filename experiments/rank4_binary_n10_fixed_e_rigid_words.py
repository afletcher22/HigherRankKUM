#!/usr/bin/env python3
"""Exact blocker-word classification for fixed-e four-block repair at binary n=10.

Builds on rank4_binary_n10_nonsimple_exact.py.

For every one of the 16 GL(4,2)-orbit representatives in the exact
two-deletion-robust binary n=10 class and every omitted label e:

* enumerate all deletion CBOs;
* connect two orders when one is obtained by a CBO-preserving permutation of
  four consecutive positions (e is held fixed; no pivots);
* compute exact distance to the successful states;
* classify blocker words up to cyclic rotation and reversal.

Finite computation only; not Lean certification.
"""

from collections import Counter, deque
from itertools import permutations
import json

import rank4_binary_n10_nonsimple_exact as base

ALL4 = tuple(p for p in permutations(range(4)) if p != (0, 1, 2, 3))


def blocker_word(columns, e, order):
    m = len(order)
    bits = []
    for i in range(m):
        tri = [order[(i + j) % m] for j in range(3)]
        vals = tuple(columns[x] for x in tri)
        bits.append(
            base.rank2(vals + (columns[e],)) == base.rank2(vals)
        )
    return tuple(int(x) for x in bits)


def canonical_word(bits):
    bits = tuple(bits)
    n = len(bits)
    rots = [bits[i:] + bits[:i] for i in range(n)]
    rb = tuple(reversed(bits))
    rots += [rb[i:] + rb[:i] for i in range(n)]
    return min(rots)


def word_string(bits):
    return "".join(str(x) for x in bits)


def four_block_neighbors(order, states):
    m = len(order)
    out = set()
    for start in range(m):
        inds = [(start + j) % m for j in range(4)]
        vals = [order[i] for i in inds]
        for patt in ALL4:
            a = list(order)
            for dst, src in enumerate(patt):
                a[inds[dst]] = vals[src]
            t = base.canonical(a)
            if t in states and t != order:
                out.add(t)
    return out


def audit_fixed_e(columns, e):
    states = set(base.deletion_cbos(columns, e))
    good = {
        o: base.successful(columns, (e, o))
        for o in states
    }
    adj = {o: set() for o in states}
    for o in states:
        for t in four_block_neighbors(o, states):
            adj[o].add(t)
            adj[t].add(o)

    dist = {o: 0 for o in states if good[o]}
    q = deque(dist)
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v not in dist:
                dist[v] = dist[u] + 1
                q.append(v)
    assert len(dist) == len(states)

    return states, good, adj, dist


def main():
    patterns, _ = base.qualifying_patterns()
    reps = base.orbit_representatives(patterns)
    assert len(reps) == 16

    dist_counts = Counter()
    words_by_distance = {}
    one_step_rigid_words = Counter()
    one_step_rigid_by_orbit = Counter()
    worst_cases = []

    for oi, (counts, orbit_size) in enumerate(reps):
        columns = base.labelled_columns(counts)
        for e in range(10):
            states, good, adj, dist = audit_fixed_e(columns, e)
            for o, d in dist.items():
                if d == 0:
                    continue
                dist_counts[d] += 1
                w = canonical_word(blocker_word(columns, e, o))
                words_by_distance.setdefault(d, Counter())[w] += 1
                if d >= 2:
                    one_step_rigid_words[w] += 1
                    one_step_rigid_by_orbit[oi] += 1
                if d == 4:
                    worst_cases.append({
                        "orbit_index": oi,
                        "omitted_label": e,
                        "word": word_string(w),
                    })

    assert dist_counts == Counter({1: 40856, 2: 2028, 3: 208, 4: 32})
    assert sum(one_step_rigid_words.values()) == 2268
    assert len(one_step_rigid_words) == 15
    assert len(words_by_distance[3]) == 4
    assert len(words_by_distance[4]) == 1
    assert set(word_string(w) for w in words_by_distance[4]) == {"000110111"}
    assert {(x["orbit_index"], x["omitted_label"]) for x in worst_cases} == {
        (2, 6), (2, 7)
    }

    out = {
        "scope": (
            "complete binary represented n=10 class satisfying exact "
            "two-deletion flat caps (2,4,6)"
        ),
        "moves": (
            "arbitrary CBO-preserving permutations of four consecutive "
            "positions; omitted element fixed; no pivots"
        ),
        "bad_states": sum(dist_counts.values()),
        "distance_histogram": dict(sorted(dist_counts.items())),
        "one_step_rigid_bad_states": sum(one_step_rigid_words.values()),
        "one_step_rigid_cyclic_reversal_word_types": len(one_step_rigid_words),
        "one_step_rigid_word_distribution": {
            word_string(k): v
            for k, v in sorted(one_step_rigid_words.items())
        },
        "word_type_count_by_distance": {
            str(d): len(words_by_distance[d])
            for d in sorted(words_by_distance)
        },
        "distance_three_word_distribution": {
            word_string(k): v
            for k, v in sorted(words_by_distance[3].items())
        },
        "distance_four_word_distribution": {
            word_string(k): v
            for k, v in sorted(words_by_distance[4].items())
        },
        "distance_four_cases": worst_cases,
        "one_step_rigid_by_orbit": {
            str(k): v for k, v in sorted(one_step_rigid_by_orbit.items())
        },
        "interpretation": (
            "Four-block rigidity collapses the exact bad-state universe to a "
            "small finite set of blocker-word types. Only four cyclic/reversal "
            "types occur at distance three, and the exact distance-four states "
            "all have the single type 000110111. This word contains both a "
            "three-blocker run and a two-blocker run, hence the certified "
            "run-geometry lemmas expose a parallel pair and a second small "
            "circuit in every worst state."
        ),
        "claim_level": "exact finite computation; not Lean certification",
    }
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
