"""Independent brute-force check of ext_local_bin.py.
interior_ext(Y): enumerate every interleaving of S (4 labelled items into the gaps after
positions 3..L-3, any order inside a gap) and test all windows directly.
Control: every length-13 survivor must have NO interior extension (brute force), and every
one-step continuation to length 14 with windows bases must have one."""
import itertools, random, sys, time
sys.path.insert(0, "bsi")
from block_bin import rank, PTS
from ext_local_bin import survivors

Svals = [1, 2, 4, 8]

def rk4(vals):
    return rank(tuple(sorted(vals)))

def interior_ext(Y):
    L = len(Y)
    gaps = list(range(3, L - 2))          # gap g = before Y[g]; needs 3 before and 3 after
    for perm in itertools.permutations(range(4)):
        # distribute perm (in order) into non-decreasing gap sequence
        for gs in itertools.combinations_with_replacement(gaps, 4):
            seq = []
            gi = 0
            for pos in range(L + 1):
                while gi < 4 and gs[gi] == pos:
                    seq.append(('s', Svals[perm[gi]])); gi += 1
                if pos < L:
                    seq.append(('y', Y[pos]))
            if all(rk4([v for _, v in seq[i:i + 4]]) == 4 for i in range(len(seq) - 3)):
                return seq
    return None

T = time.time()
cnt, level = survivors(13)
surv13 = [Y for Y, st in level]
print("L=13 survivors:", len(surv13), f"{time.time()-T:.0f}s", flush=True)
bad_control = sum(1 for Y in surv13 if interior_ext(list(Y)) is not None)
print("control: survivors that DO have an interior extension (must be 0):", bad_control, flush=True)
cont = 0; cont_fail = 0
for Y in surv13:
    for v in PTS:
        if rk4(list(Y[-3:]) + [v]) != 4:
            continue
        cont += 1
        if interior_ext(list(Y) + [v]) is None:
            cont_fail += 1
print("length-14 continuations:", cont, "without interior extension (must be 0):", cont_fail, f"{time.time()-T:.0f}s", flush=True)
rng = random.Random(1)
ok = 0
for _ in range(3000):
    Y = [rng.choice(PTS)]
    while len(Y) < 14:
        c = [v for v in PTS if rank(tuple(sorted(Y[-3:] + [v]))) == len(Y[-3:]) + 1]
        Y.append(rng.choice(c))
    ok += interior_ext(Y) is not None
print("random length-14 sequences with interior extension:", ok, "/ 3000", f"{time.time()-T:.0f}s")
