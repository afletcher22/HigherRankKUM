"""General deletable-basis (hitting) test for strict t=0 rank-4 matroids on 4k+2 elements:
is there a basis S with M-S uniformly dense, i.e. S meets every k-point and 2k-line, has >=2
elements in every 3k-plane and meets every (3k-1)-plane?  Random heavy-biased GF(p) instances."""
import sys, random, itertools, time
from collections import Counter
from kum import *
from gen import proj_points, mk
from hitting import near_tight

def span_pts(p, gens):
    pts = set()
    for coeffs in itertools.product(range(p), repeat=len(gens)):
        v = tuple(sum(c * g[i] for c, g in zip(coeffs, gens)) % p for i in range(4))
        if any(v):
            for x in v:
                if x % p:
                    inv = pow(x, p - 2, p)
                    pts.add(tuple((y * inv) % p for y in v)); break
    return sorted(pts)

def instance(p, k, rng):
    pts = proj_points(p, 4)
    n = 4 * k + 2
    for _ in range(5000):
        vecs = []
        mode = rng.choice(["plane", "line", "twoplanes", "points", "mixed"])
        if mode in ("plane", "twoplanes", "mixed"):
            for _ in range(2 if mode == "twoplanes" else 1):
                Pl = span_pts(p, rng.sample(pts, 3))
                size = rng.choice([3 * k, 3 * k - 1, 3 * k])
                base = rng.sample(Pl, min(len(Pl), rng.randint(3, 7)))
                vecs += [rng.choice(base) for _ in range(size)]
        if mode in ("line", "mixed"):
            Ln = span_pts(p, rng.sample(pts, 2))
            base = rng.sample(Ln, min(len(Ln), rng.randint(2, 4)))
            vecs += [rng.choice(base) for _ in range(rng.choice([2 * k, 2 * k - 1]))]
        if mode == "points":
            for _ in range(rng.randint(1, 4)):
                vecs += [rng.choice(pts)] * k
        base = rng.sample(pts, rng.randint(4, 9))
        while len(vecs) < n:
            vecs.append(rng.choice(base))
        rng.shuffle(vecs)
        vecs = vecs[:n]
        M = mk(p, vecs)
        if M.rank() != 4:
            continue
        info = classify(M)
        if info["strict"] and info["t"] == 0:
            return M, info
    return None, None

if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    NI = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    T = time.time()
    stats = Counter()
    for k in (3, 4, 5, 6):
        for p in (2, 3, 5):
            for it in range(NI):
                M, info = instance(p, k, rng)
                if M is None:
                    continue
                fl, NT = near_tight(M)
                kinds = tuple(sorted({(j, pc(G)) for G, j, need in NT}))
                ok = None
                for B in itertools.combinations(range(M.n), 4):
                    if M.rk(B) != 4:
                        continue
                    Bm = sum(1 << x for x in B)
                    if all(pc(G & Bm) >= need for G, j, need in NT):
                        ok = B; break
                has3k = any(j == 3 and pc(G) == 3 * k for G, j, _ in NT)
                has2k = any(j == 2 and pc(G) == 2 * k for G, j, _ in NT)
                tag = ("3k" if has3k else "") + ("2k" if has2k else "")
                stats[(k, tag or "reduced", "hit" if ok else "NO HITTING BASIS")] += 1
                if not ok:
                    print("NO HITTING BASIS k=%d p=%d" % (k, p), M.data, "profile", info["profile"], "demands", kinds, flush=True)
            print(k, p, f"{time.time()-T:.0f}s", flush=True)
    for key, v in sorted(stats.items(), key=str):
        print(key, v)
