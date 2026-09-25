"""Search for light blocked insertions in 'tetrahedral' families: B = e1..e4, most of M-B on the
six lines spanned by pairs of B (support <= 2) plus a heavy full-support point.  For every blocked
(M, B) found, classify ALL bases of M (exhaustive block search per basis type) and record which
selection rules would have avoided the bad bases:
  R1: B meets every parallel class of size k-1;
  R2: B minimises the number of elements of M-B with |supp_B| <= 2 (paving-like);
"""
import itertools, random, sys, time
from collections import Counter
from kum import *
from gen import proj_points, mk
from light_block import blocked_orders


def supp_small(M, B):
    """number of x outside B with |supp_B(x)| <= 2, i.e. x in the closure of a pair of B."""
    cnt = 0
    pairs = [M.cl(sum(1 << b for b in P)) for P in itertools.combinations(B, 2)]
    for x in range(M.n):
        if x in B:
            continue
        if any((F >> x) & 1 for F in pairs):
            cnt += 1
    return cnt


def light(M, k):
    info = classify(M)
    a, b, c = info["profile"]
    return info["strict"] and info["t"] == 0 and a <= k - 1 and b <= 2 * k - 2 and c <= 3 * k - 2


def basis_types(M):
    vals = M.data
    seen = {}
    for B in itertools.combinations(range(M.n), 4):
        if M.rk(B) != 4:
            continue
        key = tuple(sorted(map(str, (vals[x] for x in B))))
        if key not in seen:
            seen[key] = list(B)
    return list(seen.values())


def family_instance(p, k, rng):
    E = [tuple(1 if i == j else 0 for i in range(4)) for j in range(4)]
    edge_pts = set()
    for i, j in itertools.combinations(range(4), 2):
        for a in range(1, p):
            v = tuple((E[i][t] + a * E[j][t]) % p for t in range(4))
            edge_pts.add(v)
    edge_pts = sorted(edge_pts)
    full = [v for v in proj_points(p, 4) if all(x % p for x in v)]
    for _ in range(4000):
        vecs = list(E)                                   # B
        for e in E:                                      # mates of B elements
            vecs += [e] * rng.randint(0, k - 2)
        c = rng.choice(full)
        vecs += [c] * (k - 1)                            # heavy full-support point
        while len(vecs) < 4 * k + 2:
            q = rng.choice(edge_pts + edge_pts + full)
            if vecs.count(q) < k - 1:
                vecs.append(q)
        vecs = vecs[:4 * k + 2]
        M = mk(p, vecs)
        if M.rank() == 4 and light(M, k):
            return M
    return None


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    configs = [(2, 4), (2, 5), (3, 4), (3, 5)]
    stats = Counter()
    T = time.time()
    for p, k in configs:
        for it in range(int(sys.argv[2]) if len(sys.argv) > 2 else 15):
            M = family_instance(p, k, rng)
            if M is None:
                stats[(p, k, "noinst")] += 1
                continue
            B0 = [0, 1, 2, 3]
            found, st = blocked_orders(M, B0, limit=2 * 10 ** 6, rng=rng)
            if not found:
                stats[(p, k, "B0 ok" if st == "exhausted" else "B0 timeout")] += 1
                continue
            stats[(p, k, "B0 BLOCKED")] += 1
            # classify every basis type
            prof = classify(M)["profile"]
            heavy_pts = [P for P in classify(M)["flats"][1] if pc(P) == k - 1]
            rows = []
            for B in basis_types(M):
                f, s2 = blocked_orders(M, B, limit=2 * 10 ** 6, rng=rng)
                status = "BAD" if f else ("good" if s2 == "exhausted" else "timeout")
                hits = all(any((P >> b) & 1 for b in B) for P in heavy_pts)
                rows.append((status, hits, supp_small(M, B), B))
            bad = [r for r in rows if r[0] == "BAD"]
            minss = min(r[2] for r in rows)
            r1 = all(not r[1] for r in bad)                      # every bad basis misses a (k-1)-point
            r2 = all(r[2] > minss for r in bad)                  # no bad basis attains the min small-support count
            stats[(p, k, "R1 consistent" if r1 else "R1 VIOLATED")] += 1
            stats[(p, k, "R2 consistent" if r2 else "R2 VIOLATED")] += 1
            print(f"p={p} k={k} profile={prof} vals={M.data} bases={len(rows)} bad={len(bad)} "
                  f"R1={'ok' if r1 else 'VIOLATED'} R2={'ok' if r2 else 'VIOLATED'} "
                  f"bad(ss,hits)={[(r[2], r[1]) for r in bad]} min_ss={minss}", flush=True)
        print(p, k, {kk[2]: v for kk, v in stats.items() if kk[:2] == (p, k)}, f"{time.time()-T:.0f}s", flush=True)
