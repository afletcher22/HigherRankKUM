#!/usr/bin/env python3
"""Falsification audit for the post-t>0 favorable-state conjecture.

Exact:
  * all 455 simple binary rank-4 12-point subsets of PG(3,2);
  * all 15 simple binary rank-4 14-point subsets of PG(3,2).

Seeded stress test:
  * 20 universally deletion-robust simple examples for each of
    GF(3), n=12; GF(3), n=14; GF(5), n=12; GF(5), n=14.

For every pointed deletion we search for a deletion CBO admitting reinsertion
of the omitted element. Every returned witness is checked directly by testing
all cyclic rank-four windows before and after insertion.

This is finite computation, not Lean certification.
"""

from __future__ import annotations
import itertools
import json
import random
from functools import lru_cache


def inv_mod(a: int, p: int) -> int:
    return pow(a, p - 2, p)


def canon(v, p):
    v = tuple(x % p for x in v)
    for x in v:
        if x:
            z = inv_mod(x, p)
            return tuple((y * z) % p for y in v)
    raise ValueError("zero vector")


def pg3_points(p: int):
    return sorted({
        canon(v, p)
        for v in itertools.product(range(p), repeat=4)
        if any(v)
    })


def rank_ff(vs, p: int) -> int:
    if not vs:
        return 0
    A = [list(v) for v in vs]
    r = 0
    for c in range(4):
        pivot = next((i for i in range(r, len(A)) if A[i][c] % p), None)
        if pivot is None:
            continue
        A[r], A[pivot] = A[pivot], A[r]
        z = inv_mod(A[r][c] % p, p)
        A[r] = [(z * x) % p for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] % p:
                f = A[i][c] % p
                A[i] = [(A[i][j] - f * A[r][j]) % p for j in range(4)]
        r += 1
        if r == len(A):
            break
    return r


def dot(u, v, p: int) -> int:
    return sum(a * b for a, b in zip(u, v)) % p


def max_line_occupancy(M, p: int) -> int:
    best = 1
    for i, j in itertools.combinations(range(len(M)), 2):
        a, b = M[i], M[j]
        best = max(best, sum(rank_ff([a, b, x], p) <= 2 for x in M))
    return best


def max_hyperplane_occupancy(M, p: int) -> int:
    normals = pg3_points(p)
    return max(sum(dot(n, x, p) == 0 for x in M) for n in normals)


def universally_deletion_robust(M, p: int):
    """Use the exact slack-profile criterion 4*m_j+j <= n*j, j=1,2,3."""
    if rank_ff(M, p) != 4:
        return False, None
    n = len(M)
    profile = (1, max_line_occupancy(M, p), max_hyperplane_occupancy(M, p))
    ok = all(4 * profile[j - 1] + j <= n * j for j in (1, 2, 3))
    return ok, profile


def cyclic_cbo(order, p: int) -> bool:
    m = len(order)
    return all(
        rank_ff([order[(i + j) % m] for j in range(4)], p) == 4
        for i in range(m)
    )


def successful_gap(order, e, gap: int, p: int) -> bool:
    full = list(order)
    full.insert(gap, e)
    return cyclic_cbo(full, p)


def find_favorable_state(M, e_index: int, p: int):
    e = M[e_index]
    arr = [M[i] for i in range(len(M)) if i != e_index]
    m = len(arr)

    # Rotation gauge: fix arr[0] first.
    path = [0]
    remaining = tuple(range(1, m))

    @lru_cache(None)
    def basis4(indices):
        return rank_ff([arr[i] for i in indices], p) == 4

    def dfs(rem):
        if not rem:
            order = [arr[i] for i in path]
            if not cyclic_cbo(order, p):
                return None
            for gap in range(m):
                if successful_gap(order, e, gap, p):
                    return order, gap
            return None

        for x in rem:
            if len(path) >= 3 and not basis4(tuple(path[-3:] + [x])):
                continue
            path.append(x)
            nxt = tuple(y for y in rem if y != x)
            ans = dfs(nxt)
            if ans is not None:
                return ans
            path.pop()
        return None

    return dfs(remaining)


def audit_family(mats, p: int):
    pointed = 0
    prescribed_failures = []
    existential_failures = []
    for mi, M in enumerate(mats):
        fails = []
        for e in range(len(M)):
            pointed += 1
            witness = find_favorable_state(M, e, p)
            if witness is None:
                fails.append(e)
        if fails:
            prescribed_failures.append((mi, fails))
        if len(fails) == len(M):
            existential_failures.append(mi)
    return {
        "matroids": len(mats),
        "pointed_deletions": pointed,
        "prescribed_element_failures": len(prescribed_failures),
        "existential_failures": len(existential_failures),
    }


def binary_exact(n: int):
    P = pg3_points(2)
    mats = []
    for M in itertools.combinations(P, n):
        ok, _ = universally_deletion_robust(M, 2)
        if ok:
            mats.append(M)
    return audit_family(mats, 2)


def seeded_nonbinary(p: int, n: int, count: int, seed: int):
    rng = random.Random(seed)
    P = pg3_points(p)
    mats = []
    profiles = {}
    tries = 0
    while len(mats) < count:
        tries += 1
        M = tuple(rng.sample(P, n))
        ok, prof = universally_deletion_robust(M, p)
        if not ok:
            continue
        mats.append(M)
        key = ",".join(map(str, prof))
        profiles[key] = profiles.get(key, 0) + 1
    out = audit_family(mats, p)
    out["accepted_after_draws"] = tries
    out["profile_counts"] = dict(sorted(profiles.items()))
    return out


def main():
    seed = 20260920
    out = {
        "binary_exact": {
            "n12": binary_exact(12),
            "n14": binary_exact(14),
        },
        "seeded_nonbinary": {
            "gf3_n12": seeded_nonbinary(3, 12, 20, seed + 312),
            "gf3_n14": seeded_nonbinary(3, 14, 20, seed + 314),
            "gf5_n12": seeded_nonbinary(5, 12, 20, seed + 512),
            "gf5_n14": seeded_nonbinary(5, 14, 20, seed + 514),
        },
        "interpretation": {
            "binary_scope": "all simple binary rank-4 n=12 and n=14 representations inside PG(3,2)",
            "nonbinary_scope": "seeded samples only",
            "claim_level": "reproducible computation; not Lean certification",
        },
    }
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
