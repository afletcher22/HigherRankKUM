#!/usr/bin/env python3
"""Cross-field audit of rank-4 four-position repair moves.

For each listed rank-4 n=10 instance, build the complete state graph on
(e, sigma), where sigma is a CBO of M\e.

Edges:
  * point pivot: exchange e with one order entry, if the new deletion order
    is a CBO;
  * arbitrary permutation of four consecutive positions, if the resulting
    deletion order is a CBO.

The represented examples are two GF(3) and two GF(5) two-deletion-robust
instances (including parallel classes).  The sparse-paving test is the
extremal 30-block SQS(10).

This is finite computation, not Lean certification.
"""

from __future__ import annotations
import itertools
import json


REPRESENTED = [
    (3, [[1,2,2,0],[1,0,1,1],[1,1,0,0],[1,2,1,0],[1,2,2,0],
         [1,1,2,0],[1,0,0,2],[1,2,1,2],[1,1,1,1],[0,1,1,1]]),
    (3, [[1,0,1,1],[1,0,0,1],[0,1,2,2],[1,2,1,2],[0,1,0,0],
         [1,0,1,1],[0,1,2,1],[1,2,1,0],[1,2,1,0],[1,0,2,0]]),
    (5, [[0,0,1,1],[1,3,1,2],[1,4,2,0],[1,3,3,2],[1,3,4,1],
         [1,3,1,3],[1,4,3,0],[1,1,2,3],[1,3,1,0],[0,1,3,0]]),
    (5, [[1,2,4,4],[1,1,1,4],[1,3,1,1],[0,1,4,1],[0,1,3,4],
         [0,0,1,4],[1,4,0,3],[0,0,1,4],[1,4,4,2],[1,1,1,4]]),
]


def inv(a, p):
    return pow(a, p - 2, p)


def rank_ff(vectors, p):
    A = [list(v) for v in vectors]
    r = 0
    for c in range(4):
        pivot = next((i for i in range(r, len(A)) if A[i][c] % p), None)
        if pivot is None:
            continue
        A[r], A[pivot] = A[pivot], A[r]
        z = inv(A[r][c] % p, p)
        A[r] = [(z * x) % p for x in A[r]]
        for i in range(r + 1, len(A)):
            if A[i][c] % p:
                f = A[i][c] % p
                A[i] = [(A[i][j] - f * A[r][j]) % p for j in range(4)]
        r += 1
        if r == 4:
            break
    return r


def canonical(order):
    order = tuple(order)
    i = order.index(min(order))
    return order[i:] + order[:i]


def deletion_cbos(n, omitted, is_basis4):
    labels = [i for i in range(n) if i != omitted]
    first = min(labels)
    path = [first]
    out = []

    def rec(rem):
        if not rem:
            order = tuple(path)
            m = len(order)
            if all(is_basis4([order[(i+j) % m] for j in range(4)])
                   for i in range(m - 3, m)):
                out.append(order)
            return
        for x in rem:
            if len(path) >= 3 and not is_basis4(path[-3:] + [x]):
                continue
            path.append(x)
            rec([y for y in rem if y != x])
            path.pop()

    rec([x for x in labels if x != first])
    return out


def cyclic_cbo(order, is_basis4):
    m = len(order)
    return all(is_basis4([order[(i+j) % m] for j in range(4)])
               for i in range(m))


def successful(omitted, order, is_basis4):
    for gap in range(len(order)):
        full = list(order)
        full.insert(gap, omitted)
        if cyclic_cbo(full, is_basis4):
            return True
    return False


FOUR_PERMS = [
    p for p in itertools.permutations(range(4))
    if p != (0, 1, 2, 3)
]


def graph_audit(n, is_basis4):
    states = set()
    for e in range(n):
        states.update((e, o) for o in deletion_cbos(n, e, is_basis4))

    good = {s: successful(s[0], s[1], is_basis4) for s in states}
    adj = {s: set() for s in states}

    for e, order in states:
        s = (e, order)
        m = len(order)

        # Point pivots.
        for i, f in enumerate(order):
            a = list(order)
            a[i] = e
            t = (f, canonical(a))
            if t in states:
                adj[s].add(t)
                adj[t].add(s)

        # Every CBO-preserving permutation of four consecutive positions.
        for start in range(m):
            inds = [(start + j) % m for j in range(4)]
            vals = [order[i] for i in inds]
            for patt in FOUR_PERMS:
                a = list(order)
                for dst, src in enumerate(patt):
                    a[inds[dst]] = vals[src]
                t = (e, canonical(a))
                if t in states:
                    adj[s].add(t)
                    adj[t].add(s)

    unseen = set(states)
    components = []
    while unseen:
        root = unseen.pop()
        comp = {root}
        stack = [root]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if v not in comp:
                    comp.add(v)
                    unseen.discard(v)
                    stack.append(v)
        components.append(comp)

    return {
        "states": len(states),
        "successful_states": sum(good.values()),
        "components": len(components),
        "largest_component": max(map(len, components)),
        "closed_all_bad_components":
            sum(not any(good[s] for s in comp) for comp in components),
    }


def represented_audit(p, columns):
    B = {
        C for C in itertools.combinations(range(10), 4)
        if rank_ff([columns[i] for i in C], p) == 4
    }
    return graph_audit(
        10,
        lambda inds: tuple(sorted(inds)) in B,
    )


def sqs10():
    blocks = set()
    for i in range(10):
        blocks.add(frozenset((i, (i+1)%10, (i+3)%10, (i+4)%10)))
        blocks.add(frozenset((i, (i+1)%10, (i+2)%10, (i+6)%10)))
        blocks.add(frozenset((i, (i+2)%10, (i+4)%10, (i+7)%10)))
    assert len(blocks) == 30
    return frozenset(blocks)


def main():
    rows = []
    for p, cols in REPRESENTED:
        row = represented_audit(p, cols)
        row["field"] = f"GF({p})"
        row["support_size"] = len({tuple(x) for x in cols})
        row["columns"] = cols
        rows.append(row)

    H = sqs10()
    sparse = graph_audit(
        10,
        lambda inds: frozenset(inds) not in H,
    )
    sparse["circuit_hyperplanes"] = len(H)

    out = {
        "scope": "rank-4 n=10 four-block state-graph stress beyond binary",
        "represented_samples": rows,
        "sparse_paving_extremal_sqs10": sparse,
        "claim_level":
            "exact finite computation for the listed instances; not Lean certification",
    }
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
