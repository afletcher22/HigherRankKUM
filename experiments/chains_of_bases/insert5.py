"""Rank 5, three bases B1, B2, S: how much re-ordering does inserting S need?

G = orderings (pi1, pi2) making B1 B2 a cyclic basis ordering of B1 u B2 (Gabow pairs).
frozen : keep (pi1, pi2), find an order of S that fits in the gap B2|B1 or B1|B2.
keep1  : keep pi1 only (re-order B2 freely).
any    : re-order everything.
"""
import itertools, random, sys
sys.path.insert(0, '.')
import numpy as np
import cyclic_chain as C

r = 5
perms = list(itertools.permutations(range(r)))

def mm(A, B):
    return (A.astype(np.uint16) @ B.astype(np.uint16)) > 0

def study(vecs, p):
    tab = C.base_table(vecs, p, r)
    B1, B2, S = tuple(range(0, 5)), tuple(range(5, 10)), tuple(range(10, 15))
    R = lambda X, Y: C.serial_rel(X, Y, tab, perms)
    R12, R21, R1S, RS1, R2S, RS2 = R(B1, B2), R(B2, B1), R(B1, S), R(S, B1), R(B2, S), R(S, B2)
    G = R12 & R21.T                       # [pi1, pi2]
    E21 = mm(R2S, RS1).T                  # S fits between B2 and B1
    E12 = mm(R1S, RS2)                    # S fits between B1 and B2
    frozen = G & (E21 | E12)
    sol_a = R12 & E21                     # cyclic order B1 B2 S
    sol_b = E12 & R21.T                   # cyclic order B1 S B2
    p1G = G.any(axis=1); p2G = G.any(axis=0)
    p1sol = (sol_a | sol_b).any(axis=1); p2sol = (sol_a | sol_b).any(axis=0)
    return dict(G=int(G.sum()), frozen=int(frozen.sum()),
                frozen21=int((G & E21).sum()), frozen12=int((G & E12).sum()),
                keep1=int((p1G & p1sol).sum()), n1=int(p1G.sum()),
                keep2=int((p2G & p2sol).sum()), n2=int(p2G.sum()),
                any=bool((sol_a | sol_b).any()))

def report(name, rows):
    n = len(rows)
    print(name, "instances:", n)
    print("   some solution (re-order everything):      %d / %d" % (sum(x['any'] for x in rows), n))
    print("   SOME Gabow pair extends frozen:           %d / %d" % (sum(x['frozen'] > 0 for x in rows), n))
    print("   EVERY Gabow pair extends frozen:          %d / %d" % (sum(x['frozen'] == x['G'] for x in rows), n))
    fr = [x['frozen'] / x['G'] for x in rows if x['G']]
    print("   fraction of Gabow pairs extending frozen: min %.3f  mean %.3f" % (min(fr), sum(fr) / len(fr)))
    print("   EVERY Gabow order of B1 survives (B2, S free): %d / %d" % (sum(x['keep1'] == x['n1'] for x in rows), n))
    print("   EVERY Gabow order of B2 survives (B1, S free): %d / %d" % (sum(x['keep2'] == x['n2'] for x in rows), n))
    k1 = [x['keep1'] / x['n1'] for x in rows if x['n1']]
    print("   fraction of B1 orders surviving:          min %.3f  mean %.3f" % (min(k1), sum(k1) / len(k1)))
    sys.stdout.flush()

rng = random.Random(11)
circ = ['11001', '11100', '01110', '00111', '10011']
cols = [tuple(1 if i == j else 0 for i in range(5)) for j in range(5)]
cols += [tuple(int(circ[i][j]) for i in range(5)) for j in range(5)]
rows = []
for t in range(int(sys.argv[1])):
    S = C.random_bases(5, 1, 2, rng)[0]
    rows.append(study(cols + S, 2))
report("R10 pair + random binary third basis", rows)
rows = []
for t in range(int(sys.argv[2])):
    Bs = C.random_bases(5, 3, 2, rng)
    rows.append(study([v for B in Bs for v in B], 2))
report("random GF(2)", rows)
rows = []
for t in range(int(sys.argv[3])):
    Bs = C.random_bases(5, 3, 3, rng)
    rows.append(study([v for B in Bs for v in B], 3))
report("random GF(3)", rows)
