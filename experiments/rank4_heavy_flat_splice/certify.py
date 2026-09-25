"""Produce DRUP proofs (Lingeling by default; 'solver=Cadical195' to switch) for the SAT claims used by the rank-4 proof and check them with
drup_check.py.  Controls: a proof with lemmas removed must be rejected, and a one-line bogus
proof for a satisfiable formula must be rejected.

Usage: python certify.py [cyc8 cyc10 cyc12 lin14 kum6 kum8 kum10 hit14plane hit14line controls]
"""
import sys, time, random
import pysat.solvers as PS
SOLVER = 'Lingeling'
from drup_check import check

def formula(name):
    if name.startswith("cyc"):
        from cyclic_sat import build
        return build(int(name[3:]), "block", 6)[0]
    if name.startswith("lin"):
        from local_sat import build
        return build(int(name[3:]), 6)[0]
    if name in ("kum6", "kum8"):
        import kum_small_sat, itertools
        return kum_formula(int(name[3:]))
    if name == "kum10":
        from kum_4_10_sat import build
        return build(False)[0]
    if name == "kum10s":
        # strict t=0 only; the tight and t>0 cases at n=10 are covered by the Lean reductions
        from kum_4_10_sat import build
        return build(True)[0]
    if name.startswith("hit14"):
        from hit_sat14 import build
        import itertools
        cls, ids = build((3, 6, 9))
        v = lambda X, r: ids[(X, r)]
        if name == "hit14plane":
            X = (1 << 9) - 1
            return cls + [[v(X, 3)], [-v(X, 4)]]
        X = (1 << 6) - 1
        extra = [[v(X, 2)], [-v(X, 3)]]
        extra += [[v(sum(1 << x for x in c), 4)] for c in itertools.combinations(range(14), 9)]
        return cls + extra
    raise ValueError(name)

def kum_formula(N):
    # same construction as kum_small_sat.run, returned instead of solved
    import itertools
    var = lambda X, v: X * 4 + v
    pc = lambda X: bin(X).count("1")
    cl = []
    for X in range(1 << N):
        for v in range(1, 4):
            cl.append([-var(X, v + 1), var(X, v)])
        for v in range(pc(X) + 1, 5):
            cl.append([-var(X, v)])
        need = -(-4 * pc(X) // N)
        if need >= 1:
            cl.append([var(X, min(need, 4))] if need <= 4 else [])
    cl.append([var((1 << N) - 1, 4)])
    for X in range(1 << N):
        for a in range(N):
            if X >> a & 1: continue
            T = X | 1 << a
            for v in range(1, 5):
                cl.append([-var(X, v), var(T, v)])
                if v < 4: cl.append([-var(T, v + 1), var(X, v)])
            for b in range(a + 1, N):
                if X >> b & 1: continue
                U, Xb = T | 1 << b, X | 1 << b
                for v in range(1, 5):
                    c = [-var(U, v), var(T, v), var(Xb, v), var(X, v)]
                    if v >= 2: c.append(-var(X, v - 1))
                    cl.append(c)
    for rest in itertools.permutations(range(1, N)):
        if rest[0] > rest[-1]: continue
        seq = (0,) + rest
        cl.append([-var(sum(1 << seq[(i + j) % N] for j in range(4)), 4) for i in range(N)])
    return [c for c in cl if c]

def _flush_c_streams():
    """pysat reads the proof file before the C solver flushes its buffer, which silently
    truncates the proof tail on this platform; flush all C runtime streams first."""
    import ctypes, sys
    try:
        lib = ctypes.CDLL("ucrtbase") if sys.platform == "win32" else ctypes.CDLL(None)
        lib.fflush(None)
    except OSError:
        pass


def certify(name):
    t = time.time()
    cls = formula(name)
    s = getattr(PS, SOLVER)(bootstrap_with=cls, with_proof=True)
    res = s.solve()
    _flush_c_streams()
    if res:
        print(f"{name}: SAT -- nothing to certify", flush=True); return
    proof = s.get_proof()
    t1 = time.time()
    ok, msg = check(cls, proof)
    print(f"{name}: UNSAT, proof {len(proof)} lines; checker {'VERIFIED' if ok else 'REJECTED'}: {msg} "
          f"(solve {t1-t:.0f}s, check {time.time()-t1:.0f}s)", flush=True)
    return cls, proof

if __name__ == "__main__":
    args = sys.argv[1:]
    if args and args[0].startswith("solver="):
        SOLVER = args.pop(0)[7:]
    names = args or ["cyc8", "controls"]
    for nm in names:
        if nm != "controls":
            certify(nm)
    if "controls" in names:
        cls, proof = certify("cyc8")
        rng = random.Random(1)
        adds = [i for i, l in enumerate(proof) if not l.startswith("d")]
        drop = set(rng.sample(adds[:-1], len(adds) // 3))
        ok, msg = check(cls, [l for i, l in enumerate(proof) if i not in drop])
        print("control, a third of the lemmas removed (must be REJECTED):", "VERIFIED" if ok else "REJECTED", msg, flush=True)
        from cyclic_sat import build
        cls6 = build(6, "block", 6)[0]
        ok, msg = check(cls6, ["0"])
        print("control, satisfiable N=6 formula with bogus proof (must be REJECTED):", "VERIFIED" if ok else "REJECTED", msg, flush=True)
