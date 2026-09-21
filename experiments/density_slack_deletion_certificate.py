"""Exact subset checks of deletion-slack lemmas on labelled binary matroids.

This is a regression certificate, not an exhaustive classification of matroids.
Repeated nonzero vector values are distinct parallel elements. No dependencies.
"""
import json
import random
from itertools import permutations


def subset_ranks(vectors):
    spans = [1] * (1 << len(vectors))
    ranks = bytearray(len(spans))
    cache = {}
    for mask in range(1, len(spans)):
        bit = mask & -mask
        v = vectors[bit.bit_length() - 1]
        old = spans[mask ^ bit]
        key = (old, v)
        if key not in cache:
            image = sum(1 << (x ^ v) for x in range(16) if old >> x & 1)
            cache[key] = old | image
        spans[mask] = cache[key]
        ranks[mask] = spans[mask].bit_count().bit_length() - 1
    return ranks


def check(vectors):
    n = len(vectors)
    ranks = subset_ranks(vectors)
    full = len(ranks) - 1
    r = ranks[full]
    assert r == 4 and n > r
    maxima = [0] * (r + 1)
    dense = True
    strict = True
    for mask, rank in enumerate(ranks):
        size = mask.bit_count()
        maxima[rank] = max(maxima[rank], size)
        dense &= r * size <= n * rank
        if 0 < mask < full:
            strict &= r * size < n * rank
    if not dense:
        return None
    assert all(ranks[full ^ (1 << e)] == r for e in range(n))
    # Independent direct test: use each actual deletion's cardinality and rank.
    failed = 0
    for e in range(n):
        ground = full ^ (1 << e)
        mask = ground
        while mask:
            if ranks[ground] * mask.bit_count() > (n - 1) * ranks[mask]:
                failed |= 1 << e
                break
            mask = (mask - 1) & ground
    integer_slacks = [n * j - r * maxima[j] for j in range(1, r)]
    assert (failed == 0) == all(s >= j for j, s in enumerate(integer_slacks, 1))
    if strict and n % r == 0:
        assert failed == 0
    dangerous_flats = []
    if strict and n % 4 == 2:
        k = (n - 2) // 4
        predicted = 0
        for mask, rank in enumerate(ranks):
            if rank == 3 and mask.bit_count() == 3 * k + 1:
                # Check these are flats, not merely arbitrary large subsets.
                assert all(ranks[mask | (1 << e)] > 3
                           for e in range(n) if not (mask >> e & 1))
                dangerous_flats.append(mask)
                predicted |= full ^ mask
        assert predicted == failed
        complements = [full ^ flat for flat in dangerous_flats]
        assert all(a & b == 0 for i, a in enumerate(complements)
                   for b in complements[i + 1:])
        assert len(complements) <= 3
        assert n - failed.bit_count() >= k - 1
    return {"n": n, "strict": strict, "max_flat_sizes": maxima[1:r],
            "integer_slacks": integer_slacks,
            "failed_deletions": [e for e in range(n) if failed >> e & 1],
            "dangerous_hyperplanes": len(dangerous_flats)}


def main():
    witnesses = {
        "six_element_boundary_no_good_deletion": [13, 1, 14, 2, 4, 8],
        "ten_element_pair_obstruction": [1, 2, 4, 8, 1, 14, 4, 7, 6, 9],
        "eighteen_element_repair_witness":
            [1, 2, 4, 8, 1, 6, 2, 8, 1, 4, 2, 12, 1, 8, 2, 4, 5, 8],
    }
    results = {name: check(v) for name, v in witnesses.items()}
    sharp_family = []
    for k in range(1, 5):
        vectors = [1] * k + [2] * k + [8] * k + [4] * (k - 1) + [5, 6, 12]
        result = check(vectors)
        assert result['strict']
        good = len(vectors) - len(result['failed_deletions'])
        assert good == k - 1
        sharp_family.append({'k': k, 'good_deletions': good})
    insertion = []
    vectors = witnesses["ten_element_pair_obstruction"]
    ranks = subset_ranks(vectors)
    for e in range(10):
        if e in results["ten_element_pair_obstruction"]["failed_deletions"]:
            continue
        remaining = [i for i in range(10) if i != e]
        valid = extendable = 0
        first_failure = None
        histogram = {}
        for tail in permutations(remaining[1:]):
            order = (remaining[0],) + tail
            if not all(ranks[sum(1 << order[(i + j) % 9] for j in range(4))] == 4
                       for i in range(9)):
                continue
            valid += 1
            gaps = 0
            for gap in range(9):
                candidate = order[:gap] + (e,) + order[gap:]
                if all(ranks[sum(1 << candidate[(i + j) % 10] for j in range(4))] == 4
                       for i in range(10)):
                    gaps += 1
            histogram[gaps] = histogram.get(gaps, 0) + 1
            extendable += gaps > 0
            if not gaps and first_failure is None:
                first_failure = order
        insertion.append({"deleted_label": e, "deletion_cbos_mod_rotation": valid,
                          "extendable_cbos": extendable,
                          "successful_gap_histogram": histogram,
                          "first_nonextendable_order": first_failure})
    rng = random.Random(20260918)
    counts = {"tested": 0, "uniformly_dense": 0, "strict": 0,
              "strict_integral": 0, "strict_gcd_two": 0}
    for n in (8, 10, 12, 14):
        for _ in range(40):
            result = check([1, 2, 4, 8] + [rng.randrange(1, 16) for _ in range(n - 4)])
            counts["tested"] += 1
            if result is None:
                continue
            counts["uniformly_dense"] += 1
            counts["strict"] += result["strict"]
            counts["strict_integral"] += result["strict"] and n % 4 == 0
            counts["strict_gcd_two"] += result["strict"] and n % 4 == 2
    print(json.dumps({"scope": "two historical witnesses, one boundary example, and 160 seeded binary examples; all subsets exact",
                      "counts": counts, "witnesses": results,
                      "sharp_family_checks": sharp_family,
                      "ten_element_insertion_audit": insertion}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
