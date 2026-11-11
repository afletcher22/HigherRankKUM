"""One-point insertion test.

M strict uniformly dense, n = r*k.  For each e: does some CBO of M\\e have a gap
into which e can be inserted (all r windows through e are bases)?
Small brute force (DFS with window pruning).  Not a proof of anything.
"""
import itertools, random, sys


def rank_gfp(vecs, p):
    rows = [list(v) for v in vecs]
    rk = 0
    ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c] % p), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][c], p - 2, p)
        rows[rk] = [(x * inv) % p for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c] % p:
                f = rows[i][c]
                rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[rk])]
        rk += 1
    return rk


class Mat:
    def __init__(self, vecs, p, r):
        self.n, self.r = len(vecs), r
        self.bases = set()
        for c in itertools.combinations(range(self.n), r):
            if rank_gfp([vecs[i] for i in c], p) == r:
                self.bases.add(sum(1 << i for i in c))
        self.vecs, self.p = vecs, p

    def strict(self):
        n, r = self.n, self.r
        for m in range(1, n):
            for c in itertools.combinations(range(n), m):
                rk = rank_gfp([self.vecs[i] for i in c], self.p)
                if r * m >= n * rk:
                    return False
        return True


def cbos(M, elems, limit=None):
    """Yield cyclic basis orders of M restricted to elems (first element fixed)."""
    r, B = M.r, M.bases
    N = len(elems)
    seq = [elems[0]]
    used = {elems[0]}
    count = 0

    def rec():
        nonlocal count
        if len(seq) == N:
            ext = seq + seq[: r - 1]
            for i in range(N - r + 1, N):
                if sum(1 << x for x in ext[i : i + r]) not in B:
                    return
            count += 1
            yield tuple(seq)
            return
        for x in elems:
            if x in used:
                continue
            seq.append(x)
            ok = True
            if len(seq) >= r:
                ok = sum(1 << y for y in seq[-r:]) in B
            if ok:
                used.add(x)
                yield from rec()
                used.discard(x)
            seq.pop()

    for s in rec():
        yield s
        if limit and count >= limit:
            return


def free_gap(M, sigma, e):
    r, B = M.r, M.bases
    N = len(sigma)
    for j in range(N):  # insert e after position j
        new = list(sigma[: j + 1]) + [e] + list(sigma[j + 1 :])
        pos = j + 1
        L = N + 1
        if all(
            sum(1 << new[(pos - t + i) % L] for i in range(r)) in B for t in range(r)
        ):
            return True
    return False


def analyse(M, name, cap=None):
    n = M.n
    res = []
    for e in range(n):
        elems = [x for x in range(n) if x != e]
        tot = ext = 0
        for s in cbos(M, elems, cap):
            tot += 1
            if free_gap(M, s, e):
                ext += 1
        res.append((tot, ext))
    good = sum(1 for t, x in res if x > 0)
    print(name, "n=%d r=%d" % (n, M.r), "elements with an extendable deletion CBO: %d/%d" % (good, n),
          "min/max extendable fraction: %.3f / %.3f" % (
              min(x / t if t else 0 for t, x in res), max(x / t if t else 0 for t, x in res)),
          "CBO counts", sorted(set(t for t, _ in res)), flush=True)
    return good


def random_strict(r, n, p, rng, tries=2000):
    for _ in range(tries):
        vecs = []
        while len(vecs) < n:
            v = tuple(rng.randrange(p) for _ in range(r))
            if any(v):
                vecs.append(v)
        if rank_gfp(vecs, p) != r:
            continue
        M = Mat(vecs, p, r)
        if M.strict():
            return M
    return None


if __name__ == "__main__":
    rng = random.Random(1)
    # R10: [I5 | circulant]
    circ = ["11001", "11100", "01110", "00111", "10011"]
    cols = [tuple(1 if i == j else 0 for i in range(5)) for j in range(5)]
    cols += [tuple(int(circ[i][j]) for i in range(5)) for j in range(5)]
    R10 = Mat(cols, 2, 5)
    print("R10 strict:", R10.strict(), "bases:", len(R10.bases), flush=True)
    analyse(R10, "R10")
    which = sys.argv[1:] or ["3,6", "3,9", "4,8", "5,10"]
    for spec in which:
        r, n = map(int, spec.split(","))
        for p in (2, 3):
            for t in range(4):
                M = random_strict(r, n, p, rng)
                if M is None:
                    print("no strict instance found", r, n, p)
                    break
                analyse(M, "GF(%d) #%d" % (p, t))
