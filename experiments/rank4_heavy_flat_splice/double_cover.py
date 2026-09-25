"""Unified hitting lemma via double covers: checks of the paper proof.

A uniformly dense rank-4 matroid on 4k+2 elements has a double cover: 2k+1 bases with every
element in exactly two (Edmonds' partition of the doubled matroid).  The paper proof shows that
for a strict t=0 matroid with k >= 4, EVERY double cover contains a basis B with M-B uniformly
dense.  This script builds random double covers (matroid partition by augmenting paths, random
insertion orders) and asserts:
  * each demand flat has at most one victim in the cover;
  * victim-distinct 2k-lines are disjoint;
  * some basis of the cover is deletable (reported per k, including k=3 for information).
"""
import sys, random, itertools, time
from collections import Counter, deque
from kum import *
from hitting import near_tight


def double_cover(M, k, rng):
    """Partition two copies of E into 2k+1 bases of M.  Copies (e,0),(e,1)."""
    parts = [[] for _ in range(2 * k + 1)]
    where = {}
    items = [(e, c) for e in range(M.n) for c in (0, 1)]
    rng.shuffle(items)

    def indep(S):
        els = [e for e, _ in S]
        return len(set(els)) == len(els) and M.rk(els) == len(els)

    for x in items:
        # BFS in the exchange graph
        prev = {x: None}
        dq = deque([x])
        found = None
        order = list(range(len(parts)))
        rng.shuffle(order)
        while dq and found is None:
            y = dq.popleft()
            for j in order:
                if where.get(y) == j:
                    continue
                cur = [z for z in parts[j]]
                if indep(cur + [y]):
                    found = (y, j)
                    break
                for z in cur:
                    if z not in prev and indep([w for w in cur if w != z] + [y]):
                        prev[z] = (y, j)
                        dq.append(z)
        if found is None:
            raise RuntimeError("no partition (matroid not uniformly dense?)")
        # apply the shortest augmenting path: cur moves into target, its predecessor takes
        # cur's old place, and so on back to x
        cur, target = found
        while True:
            old = where.get(cur)
            if old is not None:
                parts[old].remove(cur)
            parts[target].append(cur)
            where[cur] = target
            if prev[cur] is None:
                break
            cur, target = prev[cur]
    bases = [sorted(e for e, _ in P) for P in parts]
    assert all(len(B) == 4 and M.rk(B) == 4 for B in bases)
    cnt = Counter(e for B in bases for e in B)
    assert all(cnt[e] == 2 for e in range(M.n))
    return bases


def analyse(M, k, bases):
    fl, NT = near_tight(M)
    victims = {}
    for G, j, need in NT:
        v = [i for i, B in enumerate(bases) if pc(G & sum(1 << b for b in B)) < need]
        assert len(v) <= 1, "demand flat with two victims"
        if v:
            victims[G] = (j, v[0])
    lines = [(G, v) for G, (j, v) in victims.items() if j == 2]
    for (G1, v1), (G2, v2) in itertools.combinations(lines, 2):
        if v1 != v2:
            assert G1 & G2 == 0, "victim-distinct lines meet"
    vset = {v for _, v in victims.values()}
    return len(bases) - len(vset)


if __name__ == "__main__":
    from hit_structured import build
    from hit_general import instance
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else 300
    T = time.time()
    stats = Counter()
    while time.time() - T < budget:
        k = rng.choice([3, 4, 5, 6])
        p = rng.choice([2, 3, 5])
        if rng.random() < 0.5:
            M, _ = build(p, k, rng)
        else:
            M, _ = instance(p, k, rng)
            if M is None:
                continue
        if M.rank() != 4:
            continue
        info = classify(M)
        if not info["strict"] or info["t"] != 0:
            continue
        for _ in range(3):
            bases = double_cover(M, k, rng)
            good = analyse(M, k, bases)
            stats[(k, "cover has a deletable basis" if good else "COVER WITHOUT DELETABLE BASIS")] += 1
            if not good:
                print("cover without deletable basis: k=%d" % k, M.data, bases, flush=True)
    for key, v in sorted(stats.items(), key=str):
        print(key, v)
