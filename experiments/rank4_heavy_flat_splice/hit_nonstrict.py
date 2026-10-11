"""Does the deletion route work without strictness?

Random rank-4 matroids on n = 4k+2 elements over GF(p), biased toward the non-strict structures
(a dangerous (3k+1)-plane, a tight (2k+1)-line), filtered to uniform density
(points <= k, lines <= 2k+1, planes <= 3k+1). For each, search all 4-subsets for a basis S with
M - S uniformly dense at (4k-2)/4 (points <= k-1, lines <= 2k-1, planes <= 3k-2).
Usage: python hit_nonstrict.py K N_INSTANCES SEED
"""
import itertools, random, sys


def run(k, n_inst, seed):
    n = 4 * k + 2
    full = (1 << n) - 1
    rng = random.Random(seed)
    pc = lambda m: bin(m).count("1")

    def proj_points(p):
        return [v for v in itertools.product(range(p), repeat=4)
                if any(v) and next(x for x in v if x) == 1]

    def span(p, gens):
        out = set()
        for cs in itertools.product(range(p), repeat=len(gens)):
            w = tuple(sum(c * g[i] for c, g in zip(cs, gens)) % p for i in range(4))
            if any(w):
                inv = pow(next(x for x in w if x), p - 2, p)
                out.add(tuple(x * inv % p for x in w))
        return sorted(out)

    class Mat:
        def __init__(self, p, vecs):
            self.p, self.v, self.c = p, vecs, {}

        def rk(self, m):
            if m in self.c:
                return self.c[m]
            p = self.p
            rows = [list(self.v[i]) for i in range(n) if m >> i & 1]
            r = 0
            for col in range(4):
                piv = next((i for i in range(r, len(rows)) if rows[i][col] % p), None)
                if piv is None:
                    continue
                rows[r], rows[piv] = rows[piv], rows[r]
                inv = pow(rows[r][col], p - 2, p)
                rows[r] = [x * inv % p for x in rows[r]]
                for i in range(len(rows)):
                    if i != r and rows[i][col] % p:
                        f = rows[i][col]
                        rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[r])]
                r += 1
            self.c[m] = r
            return r

        def cl(self, m):
            r = self.rk(m)
            for e in range(n):
                if not m >> e & 1 and self.rk(m | 1 << e) == r:
                    m |= 1 << e
            return m

    def flats(M):
        fl = {1: set(), 2: set(), 3: set()}
        for j in (1, 2, 3):
            for c in itertools.combinations(range(n), j):
                m = sum(1 << x for x in c)
                if M.rk(m) == j:
                    fl[j].add(M.cl(m))
        return fl

    pts = {p: proj_points(p) for p in (3, 5, 7)}

    def gen():
        p = rng.choice((3, 5, 7))
        P = pts[p]
        mode = rng.choice(["dangerous", "tight", "both", "tight2", "mix"])
        vecs = []
        if mode in ("dangerous", "both", "mix"):
            a, b, c = rng.sample(P, 3)
            pl = span(p, [a, b, c])
            pool = rng.sample(pl, min(len(pl), rng.randint(4, 9)))
            vecs += [rng.choice(pool) for _ in range(3 * k + 1)]
        if mode in ("tight", "both", "tight2", "mix"):
            a, b = rng.sample(P, 2)
            ln = span(p, [a, b])
            pool = rng.sample(ln, min(len(ln), rng.randint(3, 6)))
            vecs += [rng.choice(pool) for _ in range(2 * k + 1)]
        if mode == "tight2":
            a, b = rng.sample(P, 2)
            ln = span(p, [a, b])
            vecs += [rng.choice(ln) for _ in range(2 * k + 1)]
        base = rng.sample(P, rng.randint(3, 8))
        while len(vecs) < n:
            vecs.append(rng.choice(base))
        rng.shuffle(vecs)
        return Mat(p, vecs[:n]), mode

    stats = {"dense": 0, "strict_t0": 0, "dangerous": 0, "tight": 0, "fail": 0}
    fails = []
    caps = {1: k, 2: 2 * k + 1, 3: 3 * k + 1}
    dcap = {1: k - 1, 2: 2 * k - 1, 3: 3 * k - 2}
    tries = 0
    while stats["dense"] < n_inst and tries < 200 * n_inst:
        tries += 1
        M, mode = gen()
        if M.rk(full) != 4 or any(M.rk(1 << e) == 0 for e in range(n)):
            continue
        fl = flats(M)
        if any(pc(F) > caps[j] for j in fl for F in fl[j]):
            continue
        stats["dense"] += 1
        dang = any(pc(F) == 3 * k + 1 for F in fl[3])
        tight = any(pc(F) == 2 * k + 1 for F in fl[2])
        stats["dangerous"] += dang
        stats["tight"] += tight
        stats["strict_t0"] += not (dang or tight)
        ok = False
        for B in itertools.combinations(range(n), 4):
            S = sum(1 << x for x in B)
            if M.rk(S) == 4 and all(pc(F & ~S) <= dcap[j] for j in fl for F in fl[j]):
                ok = True
                break
        if not ok:
            stats["fail"] += 1
            fails.append((mode, M.p, M.v, dang, tight))
    print(f"k={k}", stats)
    for f in fails[:3]:
        print("FAIL", f)


if __name__ == "__main__":
    run(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
