#!/usr/bin/env python3
"""Exact side-swap obstruction audit for the hard binary n=10 orbit.

Uses orbit index 2 from the complete exact two-deletion-robust binary n=10
census, with columns (7,9,10,11,12,13,14,14,15,15).

For every omitted label and every bad deletion CBO, try the local side swap
  [a,b,c,d] -> [a,d,c,b]
at every cyclic start. Only boundary offsets -2,-1,+2,+3 can change.
Record whether an invalid move is already witnessed at one of the two
consecutive-triple extreme changed boundaries (-2,+3), or only by the
skip-one internal boundaries (-1,+2).

Finite exact computation; not Lean certification.
"""

import json
import rank4_binary_n10_nonsimple_exact as base


def side_swap(order, start):
    a = list(order)
    n = len(a)
    i = (start + 1) % n
    j = (start + 3) % n
    a[i], a[j] = a[j], a[i]
    return tuple(a)


def failed_changed_offsets(columns, order, start):
    new = side_swap(order, start)
    n = len(order)
    out = []
    for off in (-2, -1, 2, 3):
        i = (start + off) % n
        vals = tuple(columns[new[(i+j) % n]] for j in range(4))
        if base.rank2(vals) != 4:
            out.append(off)
    return tuple(out)


def main():
    patterns, _ = base.qualifying_patterns()
    reps = base.orbit_representatives(patterns)
    counts, orbit_size = reps[2]
    columns = base.labelled_columns(counts)
    assert columns == (7,9,10,11,12,13,14,14,15,15)

    expected = [
        (0,448,288,256,2336,2112,224),
        (1,512,320,256,2624,2400,224),
        (2,336,144,80,1216,1152,64),
        (3,336,144,80,1216,1152,64),
        (4,336,144,80,1216,1152,64),
        (5,336,144,80,1216,1152,64),
        (6,384,240,0,2160,1328,832),
        (7,384,240,0,2160,1328,832),
        (8,528,304,208,2528,2288,240),
        (9,528,304,208,2528,2288,240),
    ]
    rows = []
    for omitted in range(10):
        orders = base.deletion_cbos(columns, omitted)
        bad = [o for o in orders if not base.successful(columns, (omitted,o))]
        valid = invalid = extreme = internal_only = 0
        for order in bad:
            for start in range(len(order)):
                new = side_swap(order, start)
                if base.cbo(new, columns):
                    valid += 1
                    continue
                invalid += 1
                fs = failed_changed_offsets(columns, order, start)
                assert fs
                if -2 in fs or 3 in fs:
                    extreme += 1
                else:
                    internal_only += 1
        rows.append({
            "omitted_label": omitted,
            "deletion_cbos": len(orders),
            "bad_states": len(bad),
            "valid_side_swap_attempts": valid,
            "invalid_side_swap_attempts": invalid,
            "invalid_with_extreme_boundary_witness": extreme,
            "invalid_with_internal_only_witness": internal_only,
        })

    got = [
        (r["omitted_label"], r["deletion_cbos"], r["bad_states"],
         r["valid_side_swap_attempts"], r["invalid_side_swap_attempts"],
         r["invalid_with_extreme_boundary_witness"],
         r["invalid_with_internal_only_witness"])
        for r in rows
    ]
    assert got == expected

    print(json.dumps({
        "scope": "exact hard binary n=10 GL(4,2) orbit index 2",
        "orbit_size": orbit_size,
        "columns": list(columns),
        "move": "side swap (0,3,2,1), omitted element fixed",
        "changed_boundary_offsets": [-2,-1,2,3],
        "rows": rows,
        "hard_parallel_labels": [6,7],
        "hard_parallel_label_summary": {
            "bad_states_each": 240,
            "side_swap_attempts_each": 2160,
            "valid_attempts_each": 0,
            "invalid_extreme_witness_each": 1328,
            "invalid_internal_only_witness_each": 832,
        },
        "interpretation": (
            "For omitted parallel labels 6 and 7, every side-swap attempt "
            "from a bad state is invalid. More than one third are witnessed "
            "only at the internal skip-one boundaries, so the internal "
            "three-element exchange cores are essential structural data."
        ),
        "claim_level": "exact finite computation; not Lean certification",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
