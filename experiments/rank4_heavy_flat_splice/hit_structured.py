"""Structured search for strict t=0 matroids on 4k+2 elements WITHOUT a deletable basis.
Instances are built from heavy configurations (k-points, 2k-lines through them, 3k-planes
sharing lines/points) over GF(p), then completed randomly; all bases are checked."""
import sys, random, itertools, time
from collections import Counter
from kum import *
from gen import proj_points, mk
from hitting import near_tight
from hit_general import span_pts

def build(p, k, rng):
    pts = proj_points(p, 4)
    n = 4 * k + 2
    vecs = []
    mode = rng.choice(["star", "kpoints", "planes_point", "planes_line", "mix"])
    if mode == "star":                      # k-point P and 2k-lines through it
        P = rng.choice(pts)
        vecs += [P] * rng.choice([k, k, k - 1])
        for _ in range(rng.randint(2, 3)):
            d = rng.choice([v for v in pts if v != P])
            line = [v for v in span_pts(p, [P, d]) if v != P]
            vecs += [rng.choice(line) for _ in range(k)]
    elif mode == "kpoints":
        for v in rng.sample(pts, rng.randint(2, 4)):
            vecs += [v] * k
    elif mode == "planes_point":            # 3k-planes through a common point q
        q = rng.choice(pts)
        vecs += [q] * rng.randint(1, k)
        for _ in range(rng.randint(2, 4)):
            a, b = rng.sample(pts, 2)
            pl = span_pts(p, [q, a, b])
            base = rng.sample(pl, min(len(pl), rng.randint(3, 6)))
            vecs += [rng.choice(base) for _ in range(rng.randint(k, 2 * k))]
    elif mode == "planes_line":
        a, b = rng.sample(pts, 2)
        ln = span_pts(p, [a, b])
        vecs += [rng.choice(ln) for _ in range(rng.randint(2 * k - 3, 2 * k))]
        for _ in range(2):
            c = rng.choice([v for v in pts if v not in ln])
            pl = [v for v in span_pts(p, [a, b, c]) if v not in ln]
            vecs += [rng.choice(pl) for _ in range(rng.randint(k - 2, k + 1))]
    else:
        for v in rng.sample(pts, 2):
            vecs += [v] * rng.randint(k - 1, k)
        a, b, c = rng.sample(pts, 3)
        pl = span_pts(p, [a, b, c])
        vecs += [rng.choice(pl) for _ in range(rng.randint(k, 2 * k))]
    base = rng.sample(pts, rng.randint(2, 6))
    while len(vecs) < n:
        vecs.append(rng.choice(base))
    rng.shuffle(vecs)
    return mk(p, vecs[:n]), mode

def deletable(M):
    fl, NT = near_tight(M)
    for B in itertools.combinations(range(M.n), 4):
        if M.rk(B) != 4:
            continue
        Bm = sum(1 << x for x in B)
        if all(pc(G & Bm) >= need for G, j, need in NT):
            return B, NT
    return None, NT

if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else 600
    ks = [int(a) for a in sys.argv[3].split(",")] if len(sys.argv) > 3 else [4, 5]
    T = time.time()
    stats = Counter()
    while time.time() - T < budget:
        k = rng.choice(ks); p = rng.choice([2, 3, 5])
        M, mode = build(p, k, rng)
        if M.rank() != 4:
            continue
        info = classify(M)
        if not info["strict"] or info["t"] != 0:
            continue
        B, NT = deletable(M)
        nd = len(NT)
        stats[(k, mode, "ok" if B else "NO DELETABLE BASIS")] += 1
        stats[(k, "max demand flats")] = max(stats[(k, "max demand flats")], nd)
        if not B:
            print("NO DELETABLE BASIS", k, p, mode, M.data, info["profile"], flush=True)
    for key, v in sorted(stats.items(), key=str):
        print(key, v)
