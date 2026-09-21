#!/usr/bin/env python3
"""Dangerous-hyperplane spacing types in the three genuine binary n=10 failures.

For a dangerous hyperplane H containing the omitted element e, H\{e} occupies
exactly 3k=6 positions in the 9-cycle deletion CBO (k=2), so the three
outside-H positions have cyclic spacings at most four and total nine.
The only possible sorted spacing types are therefore
  (1,4,4), (2,3,4), (3,3,3).

This script exhaustively classifies those spacing types in every deletion CBO
of the three genuine eligible failures from
rank4_binary_n10_dangerous_failure_audit.py.

Finite GF(2) computation only; not Lean certification.
"""

from collections import Counter
import json
import rank4_binary_n10_dangerous_failure_audit as base


def outside_spacings(order, cols, H):
    positions = [i for i, label in enumerate(order) if cols[label] not in H]
    m = len(order)
    assert len(positions) == 3
    out = []
    for a, b in zip(positions, positions[1:] + [positions[0] + m]):
        out.append(b - a)
    return tuple(sorted(out))


def main():
    pats = base.strict_patterns()
    reps = base.orbit_reps(pats)
    rows = []

    for oi, (c, _osize) in enumerate(reps):
        cols = base.columns(c)
        Hs = base.dangerous_hypers(c)
        for e in range(10):
            orders = base.deletion_cbos(cols, e)
            if not orders:
                continue
            if any(base.insertable(cols, e, o) for o in orders):
                continue

            containing = [H for H in Hs if cols[e] in H]
            hist = Counter()
            joint = Counter()
            four_spacing_count = Counter()

            for order in orders:
                sig = tuple(sorted(outside_spacings(order, cols, H)
                                   for H in containing))
                joint[sig] += 1
                count4 = 0
                for spacings in sig:
                    hist[spacings] += 1
                    count4 += spacings.count(4)
                four_spacing_count[count4] += 1

            rows.append({
                "orbit_index": oi,
                "omitted_label": e,
                "deletion_cbos": len(orders),
                "dangerous_hyperplanes_containing_e": len(containing),
                "spacing_type_histogram": {
                    str(k): v for k, v in sorted(hist.items())
                },
                "joint_spacing_signature_histogram": {
                    str(k): v for k, v in sorted(joint.items())
                },
                "total_number_of_spacing_4s_per_cbo": {
                    str(k): v for k, v in sorted(four_spacing_count.items())
                },
            })

    assert len(rows) == 3
    for row in rows:
        assert "(3, 3, 3)" not in row["spacing_type_histogram"]

    print(json.dumps({
        "scope": "dangerous-hyperplane spacing types in all CBOs of the three genuine eligible binary n=10 failures",
        "possible_saturated_spacing_types_at_k2": [
            [1, 4, 4], [2, 3, 4], [3, 3, 3]
        ],
        "observed_failure_rows": rows,
        "balanced_333_occurrences": 0,
        "interpretation": (
            "Every dangerous hyperplane in every genuine failure CBO is "
            "unbalanced enough to contain a run of three consecutive H-points. "
            "The balanced saturated type (3,3,3), which has no such dangerous "
            "blocker triple, never occurs."
        ),
        "claim_level": "exact finite computation; not Lean certification",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
