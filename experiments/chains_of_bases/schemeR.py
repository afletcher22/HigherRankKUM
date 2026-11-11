"""Rank induction by removing one element per block ("scheme R").

M has rank r on n = r k elements.  Pick x0, and X' (k-1 further elements) so that
Q = (M / x0) restricted to Y = E - x0 - X' is a union of k disjoint bases (uniformly dense, rank r-1).
Take a cyclic basis ordering sigma of Q: every r-1 consecutive elements together with x0 form a basis
of M.  Insert x0 and the elements of X' at the k equally spaced slots of sigma.  No window contains
two inserted elements, so x at slot s is good iff x is independent of the r windows around s:
the insertion is a bipartite matching problem, and x0 is good everywhere.
"""
import itertools, random, sys
sys.path.insert(0, '.')

def rank2(vs):
    basis = []
    for v in vs:
        for b in basis:
            v = min(v, v ^ b)
        if v: basis.append(v)
    return len(basis)

def study(vecs, r, k, max_sigma=20000, rng=None):
    n = r * k
    def indep(idx): return rank2([vecs[i] for i in idx]) == len(idx)
    out = {'pairs': 0, 'pairs_Q_dense': 0, 'pairs_some_sigma_ok': 0, 'sigmas': 0, 'sigmas_ok': 0}
    for x0 in range(n):
        others = [e for e in range(n) if e != x0]
        for Xp in itertools.combinations(others, k - 1):
            out['pairs'] += 1
            Y = [e for e in others if e not in Xp]
            # sigma: cyclic order of Y, every (r-1)-window + x0 independent
            first = Y[0]; seq = [first]; used = {first}; found = []
            def rec():
                if len(found) >= max_sigma: return
                if len(seq) == len(Y):
                    ext = seq + seq[: r - 2]
                    for i in range(len(Y) - (r - 2), len(Y)):
                        if not indep(ext[i:i + r - 1] + [x0]): return
                    found.append(tuple(seq)); return
                for y in Y:
                    if y in used: continue
                    seq.append(y)
                    if len(seq) < r - 1 or indep(seq[-(r - 1):] + [x0]):
                        used.add(y); rec(); used.discard(y)
                    seq.pop()
            rec()
            if not found: continue
            out['pairs_Q_dense'] += 1
            anyok = False
            m = len(Y)
            for s in found:
                out['sigmas'] += 1
                ok = False
                for rot in range(r - 1):
                    # slots: before position rot + j(r-1), j = 0..k-1 ; windows around slot at position q:
                    slots = [rot + j * (r - 1) for j in range(k)]
                    good = {}
                    for x in Xp:
                        good[x] = [q for q in slots if all(
                            indep([s[(q - (r - 1) + t + a) % m] for a in range(r - 1)] + [x]) for t in range(r))]
                    # x0 takes one slot, X' the others injectively
                    for free in slots:
                        rest = [q for q in slots if q != free]
                        if any(all(q in good[x] for x, q in zip(Xp, perm)) for perm in itertools.permutations(rest)):
                            ok = True; break
                    if ok: break
                if ok:
                    out['sigmas_ok'] += 1; anyok = True
            if anyok: out['pairs_some_sigma_ok'] += 1
    return out

def is_dense(vecs, r, k):
    n = len(vecs)
    for m in range(1, n + 1):
        for c in itertools.combinations(range(n), m):
            if m > k * rank2([vecs[i] for i in c]): return False
    return True

if __name__ == "__main__":
    circ = ['11001', '11100', '01110', '00111', '10011']
    R10 = [1 << i for i in range(5)] + [sum(int(circ[i][j]) << i for i in range(5)) for j in range(5)]
    print("R10 (r=5,k=2):", study(R10, 5, 2), flush=True)
    rng = random.Random(2)
    for (r, k, trials) in [(3, 2, 6), (4, 2, 6), (3, 3, 4), (4, 3, 2)]:
        done = 0
        while done < trials:
            vecs = [rng.randrange(1, 1 << r) for _ in range(r * k)]
            if rank2(vecs) != r or not is_dense(vecs, r, k): continue
            res = study(vecs, r, k, max_sigma=3000)
            print("random GF(2) r=%d k=%d:" % (r, k), res, flush=True)
            done += 1
