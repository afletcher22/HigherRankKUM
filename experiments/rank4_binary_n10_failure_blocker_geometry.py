#!/usr/bin/env python3
"""Detailed blocker geometry for the three genuine eligible n=10 failures.

Depends on rank4_binary_n10_dangerous_failure_audit.py in the same directory.
For each eligible bad pointed orbit representative, this script exhaustively
checks every deletion CBO and records:
  * blocker count;
  * nonblocker run profile;
  * sizes of blocker closures;
  * how many blocker closures are dangerous hyperplanes.

Finite GF(2) computation only; not Lean certification.
"""

from collections import Counter
import json

import rank4_binary_n10_dangerous_failure_audit as base


def closure_labels(cols, labels):
    vals = tuple(cols[i] for i in labels)
    r = base.rank2(vals)
    return frozenset(
        j for j, v in enumerate(cols)
        if base.rank2(vals + (v,)) == r
    )


def blocker_word(cols, e, order):
    m = len(order)
    out = []
    for i in range(m):
        tri = tuple(order[(i + j) % m] for j in range(3))
        vals = tuple(cols[x] for x in tri)
        out.append(base.rank2(vals + (cols[e],)) == base.rank2(vals))
    return tuple(out)


def zero_run_profile(bits):
    n = len(bits)
    if all(bits):
        return ()
    start = next(i for i, b in enumerate(bits) if b)
    runs = []
    run = 0
    for t in range(1, n + 1):
        b = bits[(start + t) % n]
        if not b:
            run += 1
        elif run:
            runs.append(run)
            run = 0
    if run:
        runs.append(run)
    return tuple(sorted(runs, reverse=True))


def main():
    pats = base.strict_patterns()
    reps = base.orbit_reps(pats)

    eligible = []
    for oi, (c, _osize) in enumerate(reps):
        cols = base.columns(c)
        Hs = base.dangerous_hypers(c)
        Hlabelsets = [
            frozenset(j for j, v in enumerate(cols) if v in H)
            for H in Hs
        ]
        for e in range(10):
            orders = base.deletion_cbos(cols, e)
            if not orders:
                continue
            if any(base.insertable(cols, e, o) for o in orders):
                continue

            blocker_count = Counter()
            run_profiles = Counter()
            dangerous_blocker_count = Counter()
            closure_size_multisets = Counter()

            for order in orders:
                bits = blocker_word(cols, e, order)
                blocker_count[sum(bits)] += 1
                run_profiles[zero_run_profile(bits)] += 1

                sizes = []
                dangerous = 0
                for i, b in enumerate(bits):
                    if not b:
                        continue
                    tri = tuple(order[(i + j) % len(order)] for j in range(3))
                    C = closure_labels(cols, tri)
                    sizes.append(len(C))
                    if C in Hlabelsets:
                        dangerous += 1
                closure_size_multisets[tuple(sorted(sizes))] += 1
                dangerous_blocker_count[dangerous] += 1

            eligible.append({
                "orbit_index": oi,
                "omitted_label": e,
                "omitted_projective_point": cols[e],
                "multiplicity_vector": list(c),
                "deletion_cbos": len(orders),
                "dangerous_hyperplanes": len(Hs),
                "blocker_count_distribution": {
                    str(k): v for k, v in sorted(blocker_count.items())
                },
                "nonblocker_run_profile_distribution": {
                    str(k): v for k, v in sorted(run_profiles.items())
                },
                "dangerous_blockers_per_cbo_distribution": {
                    str(k): v for k, v in sorted(dangerous_blocker_count.items())
                },
                "blocker_closure_size_multiset_distribution": {
                    str(k): v for k, v in sorted(closure_size_multisets.items())
                },
                "minimum_dangerous_blockers_in_any_cbo":
                    min(dangerous_blocker_count),
            })

    assert len(eligible) == 3
    assert all(x["minimum_dangerous_blockers_in_any_cbo"] >= 2 for x in eligible)

    print(json.dumps({
        "scope": "three exact eligible insertion failures in strict binary n=10 orbit census",
        "eligible_failures": eligible,
        "interpretation": (
            "Dangerous blocker closures persist in every deletion CBO of every "
            "genuine failure; at least two dangerous blockers occur in each CBO."
        ),
        "claim_level": "exact finite computation; not Lean certification",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
