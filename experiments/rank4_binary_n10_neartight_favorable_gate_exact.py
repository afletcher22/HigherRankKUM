#!/usr/bin/env python3
"""Exact binary n=10 audit of the near-tight favorable Type-I gate conjecture.

For every one-step-rigid fixed-e deletion CBO in the complete represented
binary n=10 class satisfying the exact two-deletion caps (2,4,6):

1. enumerate every four-block permutation whose resulting blocker word would
   be favorable if the reordered deletion order were a CBO;
2. since the state is one-step rigid, every such candidate is CBO-invalid;
3. inspect every failed rank-four boundary window that differs from the old
   basis by exactly one element (Type-I failure);
4. compute the ambient rank-three hyperplane spanned by its retained triple.

At k=2 the candidate theorem predicts that at least one such failed favorable
Type-I gate has ambient hyperplane size >= 3k-1 = 5.

Exact finite computation; not Lean certification.
"""

from collections import Counter
from itertools import permutations
import json

import rank4_binary_n10_nonsimple_exact as base
import rank4_binary_n10_fixed_e_rigid_words as rigid

ALL4 = tuple(p for p in permutations(range(4)) if p != (0,1,2,3))


def favorable_blocker_word(columns, e, order):
    bits = rigid.blocker_word(columns, e, order)
    n = len(bits)
    return any(all(bits[(i+j)%n] == 0 for j in range(4)) for i in range(n))


def closure_labels(columns, labels):
    vals = tuple(columns[i] for i in labels)
    assert base.rank2(vals) == 3
    return frozenset(
        i for i in range(len(columns))
        if base.rank2(vals + (columns[i],)) == 3
    )


def failed_favorable_type1_gates(columns, e, order):
    n = len(order)
    rows = []

    for start in range(n):
        inds = [(start+j)%n for j in range(4)]
        vals = [order[i] for i in inds]

        for patt in ALL4:
            candidate = list(order)
            for dst, src in enumerate(patt):
                candidate[inds[dst]] = vals[src]
            candidate = tuple(candidate)

            if not favorable_blocker_word(columns, e, candidate):
                continue
            if base.cbo(candidate, columns):
                # This should never happen for a one-step-rigid state.
                rows.append({
                    "unexpected_legal_favorable": True,
                    "start": start,
                    "pattern": patt,
                })
                continue

            for i in range(n):
                oldW = frozenset(order[(i+j)%n] for j in range(4))
                newW = frozenset(candidate[(i+j)%n] for j in range(4))
                if base.rank2(tuple(columns[x] for x in newW)) == 4:
                    continue

                common = oldW & newW
                if len(common) != 3:
                    continue
                if base.rank2(tuple(columns[x] for x in common)) != 3:
                    continue

                H = closure_labels(columns, common)
                old_only = tuple(oldW - newW)
                new_only = tuple(newW - oldW)
                assert len(old_only) == 1 and len(new_only) == 1

                rows.append({
                    "unexpected_legal_favorable": False,
                    "move_start": start,
                    "pattern": patt,
                    "boundary_start": i,
                    "common": tuple(sorted(common)),
                    "outgoing": old_only[0],
                    "incoming": new_only[0],
                    "hyperplane": H,
                    "hyperplane_size": len(H),
                    "red": e in H,
                })

    return rows


def main():
    patterns, _ = base.qualifying_patterns()
    reps = base.orbit_representatives(patterns)
    assert len(reps) == 16

    total_rigid = 0
    max_size_hist = Counter()
    max_color_hist = Counter()
    min_max_size = 100
    counterexamples = []
    no_type1 = []
    threshold_cases = []
    by_orbit = Counter()

    for oi, (counts, _orbit_size) in enumerate(reps):
        columns = base.labelled_columns(counts)
        for e in range(10):
            states, good, _adj, dist = rigid.audit_fixed_e(columns, e)
            for order in states:
                if good[order] or dist[order] < 2:
                    continue

                total_rigid += 1
                by_orbit[oi] += 1
                gates = failed_favorable_type1_gates(columns, e, order)

                assert not any(x.get("unexpected_legal_favorable") for x in gates)

                gates = [x for x in gates if not x.get("unexpected_legal_favorable")]
                if not gates:
                    no_type1.append({
                        "orbit_index": oi,
                        "omitted_label": e,
                        "order": list(order),
                    })
                    counterexamples.append({
                        "orbit_index": oi,
                        "omitted_label": e,
                        "reason": "no failed favorable Type-I gate",
                    })
                    continue

                m = max(x["hyperplane_size"] for x in gates)
                min_max_size = min(min_max_size, m)
                max_size_hist[m] += 1
                colors = {
                    x["red"] for x in gates
                    if x["hyperplane_size"] == m
                }
                if colors == {True}:
                    max_color_hist["red_only"] += 1
                elif colors == {False}:
                    max_color_hist["balanced_only"] += 1
                else:
                    max_color_hist["both"] += 1

                if m == 5:
                    maxg = [x for x in gates if x["hyperplane_size"] == m]
                    threshold_cases.append({
                        "orbit_index": oi,
                        "omitted_label": e,
                        "word": rigid.word_string(
                            rigid.canonical_word(rigid.blocker_word(columns,e,order))
                        ),
                        "order": list(order),
                        "max_gate_colors": sorted(set(
                            "red" if x["red"] else "balanced" for x in maxg
                        )),
                        "max_gate_boundary_starts":
                            sorted(set(x["boundary_start"] for x in maxg)),
                        "max_gate_hyperplanes": sorted({
                            tuple(sorted(x["hyperplane"])) for x in maxg
                        }),
                    })

                if m < 5:
                    counterexamples.append({
                        "orbit_index": oi,
                        "omitted_label": e,
                        "order": list(order),
                        "word": rigid.word_string(rigid.blocker_word(columns,e,order)),
                        "max_gate_size": m,
                    })

    assert total_rigid == 2268
    assert not no_type1
    assert not counterexamples
    assert min_max_size >= 5
    assert len(threshold_cases) == 4

    out = {
        "scope": (
            "complete binary represented n=10 class satisfying exact "
            "two-deletion caps (2,4,6)"
        ),
        "one_step_rigid_states": total_rigid,
        "threshold": 5,
        "minimum_over_states_of_max_failed_favorable_type1_gate_size":
            min_max_size,
        "max_gate_size_histogram": dict(sorted(max_size_hist.items())),
        "max_gate_color_histogram": dict(sorted(max_color_hist.items())),
        "one_step_rigid_by_orbit": dict(sorted(by_orbit.items())),
        "states_with_no_failed_favorable_type1_gate": len(no_type1),
        "threshold_cases": threshold_cases,
        "counterexamples": counterexamples,
        "interpretation": (
            "Every one-step-rigid state in the complete binary n=10 class "
            "has a would-be favorable four-block permutation whose Type-I "
            "failure exposes an ambient rank-three hyperplane of size at "
            "least 3k-1=5. Thus the near-tight favorable-gate conjecture "
            "passes the exact k=2 binary census."
        ),
        "claim_level": "exact finite computation; not Lean certification",
    }
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
