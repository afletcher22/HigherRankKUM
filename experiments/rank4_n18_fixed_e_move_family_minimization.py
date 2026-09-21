#!/usr/bin/env python3
"""Seeded fixed-e move-family minimization on the historical binary t=0 n=18 witness.

This reuses the witness/state sampler from rank4_n18_four_block_type_stress.py,
but removes point pivots.  The fixed omitted element e is held constant.

Baseline move family:
  * the three adjacent transpositions inside a four-block;
  * canonical [a,b,c,d] -> [c,d,a,b]       = (2,3,0,1);
  * canonical [a,b,c,d] -> [c,d,b,a]       = (2,3,1,0);
  * endpoint swap [a,b,c,d] -> [d,b,c,a]   = (3,1,2,0).

The baseline leaves 5 of the 730 seeded bad type-states unrepaired within
depth 8.  We exhaustively test each remaining S4 permutation as one added
move type. Exactly two symmetric involutions close all 730:
  * [a,b,c,d] -> [a,d,c,b] = (0,3,2,1);
  * [a,b,c,d] -> [c,b,a,d] = (2,1,0,3).

Either augmented seven-type family repairs all 730 states within depth <= 6.

Finite seeded computation only; not exhaustive over all deletion CBOs and
not Lean certification.
"""

from collections import Counter, deque
from itertools import permutations
import json

import rank4_n18_four_block_type_stress as base

ADJ = (
    (1,0,2,3),
    (0,2,1,3),
    (0,1,3,2),
)
BASE_NONADJ = (
    (2,3,0,1),
    (2,3,1,0),
    (3,1,2,0),
)
WORKING_EXTRAS = (
    (0,3,2,1),
    (2,1,0,3),
)
ALL4 = tuple(p for p in permutations(range(4)) if p != (0,1,2,3))


def fixed_e_neighbors(state, patterns):
    e, s = state
    s = list(s)
    n = len(s)
    out = set()
    for p in patterns:
        for q in range(n):
            ii = [(q+j) % n for j in range(4)]
            z = [s[i] for i in ii]
            a = s.copy()
            for d, src in enumerate(p):
                a[ii[d]] = z[src]
            if base.cbo(a):
                out.add((e, base.canon(a)))
    return out


def distance_to_success(start, patterns, maxdepth=8):
    start = (start[0], base.canon(start[1]))
    if base.gaps(*start):
        return 0
    seen = {start}
    q = deque([(start, 0)])
    while q:
        u, d = q.popleft()
        if d == maxdepth:
            continue
        for v in fixed_e_neighbors(u, patterns):
            if v in seen:
                continue
            seen.add(v)
            if base.gaps(*v):
                return d + 1
            q.append((v, d + 1))
    return None


def sampled_bad_states():
    bad = {}
    for e in base.TYPES:
        S = set()
        for j in range(120):
            s = base.find_cbo(e, 1000 + j)
            if s is not None and base.gaps(e, s) == 0:
                S.add(base.canon(s))
        bad[e] = S
    assert sum(map(len, bad.values())) == 730
    return bad


def audit(bad, patterns, maxdepth=8):
    hist = Counter()
    failures = []
    for e, S in bad.items():
        for s in S:
            d = distance_to_success((e, s), patterns, maxdepth=maxdepth)
            if d is None:
                failures.append((e, s))
            else:
                hist[d] += 1
    return hist, failures


def main():
    bad = sampled_bad_states()
    baseline = ADJ + BASE_NONADJ
    h0, f0 = audit(bad, baseline)
    assert len(f0) == 5

    candidates = [p for p in ALL4 if p not in baseline]
    working = []
    rows = []
    for p in candidates:
        h, failures = audit(bad, baseline + (p,))
        row = {
            "permutation": list(p),
            "failures_within_depth_8": len(failures),
        }
        if not failures:
            row["maximum_depth"] = max(h)
            row["distance_histogram"] = dict(sorted(h.items()))
            working.append(p)
        rows.append(row)

    assert tuple(working) == WORKING_EXTRAS
    for p in working:
        h, failures = audit(bad, baseline + (p,))
        assert not failures
        assert max(h) == 6

    print(json.dumps({
        "scope": (
            "historical strict binary t=0 n=18 witness; "
            "730 seeded bad parallel-type states"
        ),
        "state_constraint": "omitted element fixed; no point pivots",
        "baseline_move_types": {
            "adjacent_transpositions": [list(p) for p in ADJ],
            "nonadjacent_patterns": [list(p) for p in BASE_NONADJ],
            "failures_within_depth_8": len(f0),
            "distance_histogram_for_repaired_states": dict(sorted(h0.items())),
        },
        "single_extra_search": rows,
        "working_single_extras": [list(p) for p in working],
        "interpretation": (
            "All 23 nonidentity S4 permutations are unnecessary on this "
            "historical stress set. Starting from the six-type baseline, "
            "exactly two symmetric involutions work as a single additional "
            "move type; either gives a seven-type fixed-e family repairing "
            "all 730 seeded bad states within depth at most 6."
        ),
        "claim_level": (
            "seeded finite computation; not exhaustive and not Lean certified"
        ),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
