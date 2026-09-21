#!/usr/bin/env python3
"""Exact binary n=10 two-deletion-robust favorable-state audit.

Scope:
  labelled rank-4 binary matroids represented by 10 nonzero GF(2)^4 columns,
  allowing parallel columns, modulo projective scaling (trivial over GF(2)).

The exact two-deletion-robust density caps are:
  rank-1 flat <= 2, rank-2 flat <= 4, rank-3 flat <= 6.

The script:
  1. enumerates every multiplicity vector c in {0,1,2}^15 with sum(c)=10;
  2. keeps exactly those satisfying the three caps;
  3. quotients the 28,476 survivors by GL(4,2);
  4. exhaustively checks every omitted label on one representative per orbit;
  5. builds the full (e,sigma) state graph for each orbit representative;
  6. tests closed all-bad components under
       a) adjacent CBO-preserving swaps + point pivots;
       b) arbitrary single transpositions + point pivots.

This is exact finite computation, not Lean certification.
"""

from __future__ import annotations

from collections import Counter, deque
from functools import lru_cache
from itertools import combinations, permutations, product
import json


def rank2(values):
    pivots = [0] * 4
    r = 0
    for value in values:
        x = value
        while x:
            i = x.bit_length() - 1
            if pivots[i]:
                x ^= pivots[i]
            else:
                pivots[i] = x
                r += 1
                break
    return r


POINTS = tuple(range(1, 16))


def span_points(a, b):
    return frozenset(x for x in POINTS if rank2((a, b, x)) <= 2)


LINES = sorted({span_points(a, b) for a, b in combinations(POINTS, 2)},
               key=lambda s: tuple(sorted(s)))


def dot_bits(a, b):
    return (a & b).bit_count() & 1


HYPERPLANES = tuple(
    frozenset(x for x in POINTS if dot_bits(n, x) == 0)
    for n in POINTS
)


def occupancy_profile(counts):
    def occ(flat):
        return sum(counts[x - 1] for x in flat)
    return (
        max(counts),
        max(map(occ, LINES)),
        max(map(occ, HYPERPLANES)),
    )


def qualifying_patterns():
    out = set()
    by_doubles = Counter()
    for d in range(6):
        singles = 10 - 2 * d
        support_size = d + singles
        if singles < 0 or support_size > 15:
            continue
        for support in combinations(range(15), support_size):
            for doubled in combinations(support, d):
                c = [0] * 15
                for i in support:
                    c[i] = 1
                for i in doubled:
                    c[i] = 2
                c = tuple(c)
                m1, m2, m3 = occupancy_profile(c)
                if (m1, m2, m3) <= (2, 4, 6):
                    out.add(c)
                    by_doubles[d] += 1
    return out, by_doubles


def independent4(cols):
    return rank2(cols) == 4


def gl_permutations():
    # Images of the four coordinate basis vectors are an ordered basis.
    basis_vecs = (1, 2, 4, 8)
    out = []
    for imgs in permutations(POINTS, 4):
        if not independent4(imgs):
            continue
        perm = []
        for x in POINTS:
            y = 0
            for j, ej in enumerate(basis_vecs):
                if x & ej:
                    y ^= imgs[j]
            perm.append(y - 1)
        out.append(tuple(perm))
    assert len(out) == 20160
    return out


def apply_perm(counts, perm):
    out = [0] * 15
    for i, c in enumerate(counts):
        out[perm[i]] = c
    return tuple(out)


def orbit_representatives(patterns):
    group = gl_permutations()
    unseen = set(patterns)
    reps = []
    while unseen:
        c = min(unseen)
        orb = {apply_perm(c, g) for g in group}
        orb &= patterns
        unseen -= orb
        reps.append((c, len(orb)))
    return reps


def labelled_columns(counts):
    out = []
    for i, c in enumerate(counts):
        out.extend([i + 1] * c)
    assert len(out) == 10
    return tuple(out)


def cbo(order, columns):
    m = len(order)
    return all(
        rank2(tuple(columns[order[(i + j) % m]] for j in range(4))) == 4
        for i in range(m)
    )


def deletion_cbos(columns, omitted):
    labels = [i for i in range(10) if i != omitted]
    first = min(labels)
    path = [first]
    out = []

    def rec(rem):
        if not rem:
            order = tuple(path)
            if cbo(order, columns):
                out.append(order)
            return
        for x in rem:
            if len(path) >= 3:
                vals = tuple(columns[i] for i in path[-3:] + [x])
                if rank2(vals) != 4:
                    continue
            path.append(x)
            rec([y for y in rem if y != x])
            path.pop()

    rec([x for x in labels if x != first])
    return out


def canonical(order):
    order = tuple(order)
    i = order.index(min(order))
    return order[i:] + order[:i]


def successful(columns, state):
    e, order = state
    for gap in range(len(order)):
        full = list(order)
        full.insert(gap, e)
        if cbo(tuple(full), columns):
            return True
    return False


def states(columns):
    out = set()
    per_e = {}
    for e in range(10):
        os = deletion_cbos(columns, e)
        per_e[e] = len(os)
        out.update((e, o) for o in os)
    return out, per_e


def graph_audit(columns, swap_mode):
    S, per_e = states(columns)
    good = {s: successful(columns, s) for s in S}
    adj = {s: set() for s in S}

    for e, order in S:
        m = len(order)
        pairs = (
            combinations(range(m), 2)
            if swap_mode == "transposition"
            else ((i, (i + 1) % m) for i in range(m))
        )
        for i, j in pairs:
            a = list(order)
            a[i], a[j] = a[j], a[i]
            t = (e, canonical(a))
            if t in S:
                adj[(e, order)].add(t)

        # Point pivot: exchange omitted e with one present label.
        for i, f in enumerate(order):
            a = list(order)
            a[i] = e
            t = (f, canonical(a))
            if t in S:
                adj[(e, order)].add(t)

    unseen = set(S)
    comps = []
    bad_sizes = []
    while unseen:
        root = unseen.pop()
        comp = {root}
        q = [root]
        while q:
            u = q.pop()
            for v in adj[u]:
                if v not in comp:
                    comp.add(v)
                    unseen.discard(v)
                    q.append(v)
        comps.append(comp)
        if not any(good[x] for x in comp):
            bad_sizes.append(len(comp))

    return {
        "states": len(S),
        "successful_states": sum(good.values()),
        "components": len(comps),
        "largest_component": max(map(len, comps)),
        "closed_all_bad_components": len(bad_sizes),
        "closed_all_bad_component_sizes": dict(sorted(Counter(bad_sizes).items())),
        "deletion_cbos_per_label": per_e,
    }


def prescribed_element_audit(columns):
    failures = []
    cbo_counts = {}
    for e in range(10):
        os = deletion_cbos(columns, e)
        cbo_counts[e] = len(os)
        if not any(successful(columns, (e, o)) for o in os):
            failures.append(e)
    return failures, cbo_counts


def main():
    patterns, by_doubles = qualifying_patterns()
    assert len(patterns) == 28476

    reps = orbit_representatives(patterns)
    assert len(reps) == 16
    assert sum(size for _, size in reps) == len(patterns)

    rows = []
    total_prescribed_failures = 0
    orbits_with_adjacent_closed_bad = 0
    orbits_with_transposition_closed_bad = 0

    for idx, (counts, orbit_size) in enumerate(reps):
        columns = labelled_columns(counts)
        failures, _ = prescribed_element_audit(columns)
        total_prescribed_failures += len(failures)

        adj = graph_audit(columns, "adjacent")
        trans = graph_audit(columns, "transposition")
        if adj["closed_all_bad_components"]:
            orbits_with_adjacent_closed_bad += 1
        if trans["closed_all_bad_components"]:
            orbits_with_transposition_closed_bad += 1

        rows.append({
            "orbit_index": idx,
            "orbit_size": orbit_size,
            "multiplicity_vector": list(counts),
            "flat_occupancy_profile": list(occupancy_profile(counts)),
            "prescribed_element_failures": failures,
            "adjacent_swaps_plus_pivots": adj,
            "all_transpositions_plus_pivots": trans,
        })

    out = {
        "scope": "exact binary rank-4 n=10 represented multisets with two-deletion density robustness",
        "qualifying_multiplicity_patterns": len(patterns),
        "qualifying_by_number_of_doubled_projective_points": dict(sorted(by_doubles.items())),
        "gl4_2_orbits": len(reps),
        "total_prescribed_element_failures_on_orbit_representatives": total_prescribed_failures,
        "orbits_with_closed_all_bad_component_adjacent_plus_pivots":
            orbits_with_adjacent_closed_bad,
        "orbits_with_closed_all_bad_component_transpositions_plus_pivots":
            orbits_with_transposition_closed_bad,
        "orbits": rows,
        "interpretation": {
            "lifting": (
                "Every omitted label is favorable in every GL(4,2) orbit "
                "representative, so the exact non-simple binary n=10 class "
                "contains no prescribed-element counterexample."
            ),
            "state_graph": (
                "Closed all-bad components exist for the natural adjacent-swap "
                "+ pivot graph, and persist in one orbit even after every "
                "single transposition is allowed. Therefore component-wise "
                "escape is not a valid universal proof target."
            ),
        },
        "claim_level": "exact finite computation; not Lean certification",
    }
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
