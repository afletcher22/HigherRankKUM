"""Random strict t=0 rank-4 GF(p) instances with a prescribed 3k-plane H={x3=0}."""
import itertools, random
from kum import *


def proj_points(p, dim):
    pts = set()
    for v in itertools.product(range(p), repeat=dim):
        if any(v):
            for x in v:
                if x % p:
                    inv = pow(x, p - 2, p)
                    pts.add(tuple((y * inv) % p for y in v))
                    break
    return sorted(pts)


def mk(p, vecs):
    if p == 2:
        cols = [sum((v[i] % 2) << i for i in range(4)) for v in vecs]
        return binary(cols)
    return gfp(vecs, p)


def instance_with_plane(p, k, rng, mode="mixed", tries=3000):
    n = 4 * k + 2
    plane = [v + (0,) for v in proj_points(p, 3)]
    space = proj_points(p, 4)
    outside = [v for v in space if v[3] % p]
    for _ in range(tries):
        # H part
        base = rng.sample(plane, rng.randint(3, min(len(plane), 3 * k)))
        H = []
        rep = rng.choice([0.0, 0.3, 0.6])
        while len(H) < 3 * k:
            H.append(rng.choice(H) if H and rng.random() < rep else rng.choice(base))
        # R part
        if mode == "line" or (mode == "mixed" and rng.random() < 0.3):
            a, b = rng.sample(outside, 2)
            line = sorted({tuple((x * s + y * t) % p for x, y in zip(a, b))
                           for s in range(p) for t in range(p) if (s, t) != (0, 0)})
            line = [v for v in line if any(v)]
            # normalise
            def norm(v):
                for x in v:
                    if x % p:
                        inv = pow(x, p - 2, p)
                        return tuple((y * inv) % p for y in v)
            line = sorted({norm(v) for v in line if v[3] % p})
            pool = line
        else:
            pool = rng.sample(outside, rng.randint(2, min(len(outside), k + 2)))
        R = []
        rep2 = rng.choice([0.0, 0.4, 0.7])
        while len(R) < k + 2:
            R.append(rng.choice(R) if R and rng.random() < rep2 else rng.choice(pool))
        vecs = H + R
        M = mk(p, vecs)
        if M.rank() != 4:
            continue
        info = classify(M)
        if not info["strict"] or info["t"] != 0:
            continue
        Hmask = (1 << (3 * k)) - 1
        if Hmask not in info["planes3k"]:
            continue
        return M, Hmask, info
    return None
