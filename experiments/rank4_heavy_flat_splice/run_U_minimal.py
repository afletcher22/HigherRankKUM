"""Which heaviness breaks universal contiguous splicing?  Instances that are light except for ONE
feature: (pl) a (3k-1)-plane, (ln) a (2k-1)-line, (pt) a k-point.  Exhaustive blocked-order search
for the most degenerate bases."""
import random, sys, time, itertools
from collections import Counter
from kum import *
from gen import proj_points, mk
from light_block import blocked_orders
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 3)


def degenerate_bases(M, num):
    """bases ranked by degeneracy: elements in planes/lines spanned by subsets of B (more = worse)"""
    cands = []
    for _ in range(400):
        B = rng.sample(range(M.n), 4)
        if M.rk(B) < 4:
            continue
        score = sum(pc(M.cl(sum(1 << x for x in T))) for T in itertools.combinations(B, 3))
        score += 2 * sum(pc(M.cl(sum(1 << x for x in T))) for T in itertools.combinations(B, 2))
        cands.append((score, sorted(B)))
    cands.sort(reverse=True)
    out, seen = [], set()
    for s, B in cands:
        if tuple(B) not in seen:
            seen.add(tuple(B)); out.append((s, B))
        if len(out) >= num:
            break
    return out


def norm(v, p):
    for x in v:
        if x % p:
            inv = pow(x, p - 2, p)
            return tuple((y * inv) % p for y in v)


def inst(p, k, kind):
    pts = proj_points(p, 4)
    for _ in range(20000):
        if kind == "pt":
            vecs = [rng.choice(pts)] * k
        elif kind == "ln":
            a, b = rng.sample(pts, 2)
            line = sorted({norm(tuple((x * s + y * t) % p for x, y in zip(a, b)), p)
                           for s in range(p) for t in range(p) if (s, t) != (0, 0)})
            vecs = []
            while len(vecs) < 2 * k - 1:
                q = rng.choice(line)
                if vecs.count(q) < k - 1:
                    vecs.append(q)
        else:
            plane = [v for v in pts if v[3] == 0]
            vecs = []
            while len(vecs) < 3 * k - 1:
                q = rng.choice(plane)
                if vecs.count(q) < k - 1:
                    vecs.append(q)
        pool = rng.sample(pts, min(len(pts), 3 * k))
        while len(vecs) < 4 * k + 2:
            q = rng.choice(pool)
            if vecs.count(q) < k - 1:
                vecs.append(q)
        M = mk(p, vecs)
        info = classify(M)
        if not (info["strict"] and info["t"] == 0):
            continue
        a, b, c = info["profile"]
        want = {"pt": (a == k and b <= 2 * k - 2 and c <= 3 * k - 2),
                "ln": (a <= k - 1 and b == 2 * k - 1 and c <= 3 * k - 2),
                "pl": (a <= k - 1 and b <= 2 * k - 2 and c == 3 * k - 1)}[kind]
        if want:
            return M, info["profile"]
    return None


if __name__ == "__main__":
    c = Counter()
    T = time.time()
    for k, p in ((3, 3), (3, 5), (4, 3)):
        for kind in ("pl", "ln", "pt"):
            for it in range(4 if k == 3 else 2):
                r = inst(p, k, kind)
                if r is None:
                    c[(k, kind, "noinst")] += 1
                    continue
                M, prof = r
                for score, B in degenerate_bases(M, 3):
                    found, st = blocked_orders(M, B, limit=4 * 10 ** 5, rng=rng)
                    key = (k, kind, "BLOCKED" if found else ("none-exh" if st == "exhausted" else "timeout"))
                    c[key] += 1
                    if found:
                        print("BLOCKED", k, kind, p, prof, M.data, "B", B, "sigma", found[0], flush=True)
            print(k, p, kind, {kk[2]: v for kk, v in c.items() if kk[:2] == (k, kind)}, f"{time.time()-T:.0f}s", flush=True)
