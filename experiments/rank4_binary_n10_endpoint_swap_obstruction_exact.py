#!/usr/bin/env python3
"""Exact endpoint-swap obstruction audit for the hard binary n=10 orbit.

Uses orbit index 2 from the complete exact two-deletion-robust binary n=10
census.  Its labelled columns are
  (7,9,10,11,12,13,14,14,15,15).

For every omitted label and every bad deletion CBO, try the local endpoint
swap
  [a,b,c,d] -> [d,b,c,a]
at every cyclic start.  If the resulting deletion order is not a CBO, record
whether one of the two extreme boundary windows (offset -3 or +3) already
fails, or whether the obstruction is visible only at an internal boundary.

This isolates the role of endpoint swaps as structural probes.  In
particular, for the two parallel labels 6 and 7 supporting the deepest exact
obstruction, no endpoint swap from any bad state is CBO-preserving.

Finite exact computation; not Lean certification.
"""

import json

import rank4_binary_n10_nonsimple_exact as base


def endpoint_swap(order, start):
    a = list(order)
    n = len(a)
    i = start % n
    j = (start + 3) % n
    a[i], a[j] = a[j], a[i]
    return tuple(a)


def failed_boundary_offsets(columns, order, start):
    new = endpoint_swap(order, start)
    n = len(order)
    out = []
    for off in (-3, -2, -1, 1, 2, 3):
        i = (start + off) % n
        vals = tuple(columns[new[(i + j) % n]] for j in range(4))
        if base.rank2(vals) != 4:
            out.append(off)
    return tuple(out)


def main():
    patterns, _ = base.qualifying_patterns()
    reps = base.orbit_representatives(patterns)
    counts, orbit_size = reps[2]
    columns = base.labelled_columns(counts)

    assert columns == (7,9,10,11,12,13,14,14,15,15)

    rows = []
    for omitted in range(10):
        orders = base.deletion_cbos(columns, omitted)
        bad = [o for o in orders
               if not base.successful(columns, (omitted, o))]

        valid = 0
        invalid = 0
        extreme_witness = 0
        internal_only = 0

        for order in bad:
            for start in range(len(order)):
                new = endpoint_swap(order, start)
                if base.cbo(new, columns):
                    valid += 1
                    continue
                invalid += 1
                fails = failed_boundary_offsets(columns, order, start)
                assert fails
                if -3 in fails or 3 in fails:
                    extreme_witness += 1
                else:
                    internal_only += 1

        rows.append({
            "omitted_label": omitted,
            "deletion_cbos": len(orders),
            "bad_states": len(bad),
            "valid_endpoint_swap_attempts": valid,
            "invalid_endpoint_swap_attempts": invalid,
            "invalid_with_extreme_boundary_witness": extreme_witness,
            "invalid_with_internal_only_witness": internal_only,
        })

    expected = [
        (0,448,288,192,2400,2240,160),
        (1,512,320,192,2688,2464,224),
        (2,336,144,112,1184,1128,56),
        (3,336,144,112,1184,1128,56),
        (4,336,144,112,1184,1128,56),
        (5,336,144,112,1184,1128,56),
        (6,384,240,0,2160,1440,720),
        (7,384,240,0,2160,1440,720),
        (8,528,304,256,2480,2288,192),
        (9,528,304,256,2480,2288,192),
    ]
    got = [
        (r["omitted_label"], r["deletion_cbos"], r["bad_states"],
         r["valid_endpoint_swap_attempts"],
         r["invalid_endpoint_swap_attempts"],
         r["invalid_with_extreme_boundary_witness"],
         r["invalid_with_internal_only_witness"])
        for r in rows
    ]
    assert got == expected

    hard = [rows[6], rows[7]]
    assert all(r["valid_endpoint_swap_attempts"] == 0 for r in hard)
    assert all(r["invalid_endpoint_swap_attempts"] == 2160 for r in hard)
    assert all(r["invalid_with_internal_only_witness"] == 720 for r in hard)

    print(json.dumps({
        "scope": "exact hard binary n=10 GL(4,2) orbit index 2",
        "orbit_size": orbit_size,
        "columns": list(columns),
        "move": "endpoint swap (3,1,2,0), omitted element fixed",
        "rows": rows,
        "hard_parallel_labels": [6,7],
        "hard_parallel_label_summary": {
            "bad_states_each": 240,
            "endpoint_swap_attempts_each": 2160,
            "valid_attempts_each": 0,
            "invalid_extreme_witness_each": 1440,
            "invalid_internal_only_witness_each": 720,
        },
        "interpretation": (
            "For the two omitted parallel labels supporting the deepest exact "
            "obstruction, endpoint swaps never preserve the deletion CBO. "
            "They act purely as structural probes. One third of their failed "
            "attempts have no extreme (-3 or +3) failed boundary window, so a "
            "proof based only on the two consecutive-triple extreme cores is "
            "insufficient; the four internal single-exchange cores are "
            "genuinely required."
        ),
        "claim_level": "exact finite computation; not Lean certification",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
