"""Choice-lemma test for a dangerous plane, strict case, general k.

M: rank 4 on n = 4k+2 elements, strict (points <= k, lines <= 2k, planes <= 3k+1) with a
(3k+1)-plane P. Take a partition of P into k independent triples D_1..D_k and one leftover e0.
Claim: for EVERY such partition there are i and c in C = E - P with D_i + c deletable.
Also reports how often each rule-based choice works.
Usage: python dangerous_choice.py K N_INSTANCES SEED
"""
import itertools, random, sys


def main(k, n_inst, seed):
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

    pts = {p: proj_points(p) for p in (5, 7, 11)}
    caps = {1: k, 2: 2 * k, 3: 3 * k + 1}
    dcap = {1: k - 1, 2: 2 * k - 1, 3: 3 * k - 2}

    def partitions(M, P, limit):
        """Up to `limit` random partitions of P into k independent triples plus one leftover."""
        Ps = [x for x in range(n) if P >> x & 1]
        found = []
        for _ in range(limit * 20):
            rng.shuffle(Ps)
            left = list(Ps)
            triples = []
            ok = True
            for _t in range(k):
                cand = [t for t in itertools.combinations(left, 3)
                        if M.rk(sum(1 << x for x in t)) == 3]
                if not cand:
                    ok = False
                    break
                t = rng.choice(cand)
                triples.append(sum(1 << x for x in t))
                left = [x for x in left if x not in t]
            if ok:
                found.append((triples, left[0]))
                if len(found) >= limit:
                    break
        return found

    stats = {"inst": 0, "partitions": 0, "fail": 0, "multiDanger": 0}
    tries = 0
    while stats["inst"] < n_inst and tries < 300 * n_inst:
        tries += 1
        p = rng.choice((5, 7, 11))
        P0 = pts[p]
        a, b, c = rng.sample(P0, 3)
        pl = span(p, [a, b, c])
        pool = rng.sample(pl, min(len(pl), rng.randint(5, 3 * k + 1)))
        vecs = [rng.choice(pool) for _ in range(3 * k + 1)]
        off = [v for v in P0 if v not in set(pl)]
        mode = rng.randint(0, 4)
        if mode >= 3:
            # two dangerous planes P, P' meeting in a 2k-line, or C containing a k-point
            a, b, c = rng.sample(P0, 3)
            line = span(p, [a, b])
            full1 = set(span(p, [a, b, c]))
            if len(full1) <= len(line):
                continue
            d = rng.choice([v for v in P0 if v not in full1])
            pi1 = [v for v in full1 if v not in set(line)]
            pi2 = [v for v in span(p, [a, b, d]) if v not in set(line)]
            lp = rng.sample(line, min(len(line), rng.randint(2, 4)))
            vecs = [rng.choice(lp) for _ in range(2 * k)]
            vecs += [rng.choice(pi1) for _ in range(k + 1)]
            if mode == 3:
                vecs += [rng.choice(pi2) for _ in range(k + 1)]
            else:
                q = rng.choice(pi2)
                vecs += [q] * k + [rng.choice(off)]
        elif mode == 0:
            d, e = rng.sample(off, 2)
            ln = [v for v in span(p, [d, e]) if v not in set(pl)]
            vecs += [rng.choice(ln) for _ in range(k + 1)]
        elif mode == 1:
            d = rng.choice(off)
            pl2 = [v for v in span(p, [a, b, d]) if v not in set(pl)]
            vecs += [rng.choice(pl2) for _ in range(k + 1)]
        else:
            vecs += rng.sample(off, k + 1)
        M = Mat(p, vecs)
        if M.rk(full) != 4 or any(M.rk(1 << x) == 0 for x in range(n)):
            continue
        fl = flats(M)
        if any(pc(F) > caps[j] for j in fl for F in fl[j]):
            continue
        dangers = [F for F in fl[3] if pc(F) == 3 * k + 1]
        if not dangers:
            continue
        stats["inst"] += 1
        stats["multiDanger"] += len(dangers) > 1
        for P in dangers:
            C = full & ~P
            for triples, e0 in partitions(M, P, 4):
                stats["partitions"] += 1
                good = False
                for D in triples:
                    for cc in range(n):
                        if not C >> cc & 1:
                            continue
                        S = D | 1 << cc
                        if M.rk(S) == 4 and all(pc(F & ~S) <= dcap[j] for j in fl for F in fl[j]):
                            good = True
                            break
                    if good:
                        break
                if not good:
                    stats["fail"] += 1
                    print("FAIL", p, vecs, triples, e0, flush=True)
    print(f"k={k}", stats)


if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
