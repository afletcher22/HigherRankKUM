"""Write the CNFs of two candidate claims for the n=10 strict t=0 case to certs/:

  kum10l  strict t=0 KUM(4,10) with no 6-plane and no 4-line (every 6-set has rank 4, every
          4-set rank at least 3): the case left after Theorems G and L4 at k=2;
  xcyc6   the extension theorem X' on 6 elements (cyclic), as in ext_witness.py.
"""
import os
from cert_measure import OUT
import kum_4_10_sat as K
from ext_witness import build_cyclic


def write(name, cls):
    nv = max(abs(l) for c in cls for l in c)
    with open(os.path.join(OUT, f"{name}.cnf"), "w", newline="\n") as f:
        f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    print(name, len(cls), "clauses", flush=True)


cl, _ = K.build(True)
write("kum10l", cl + K.no_big(3, 6) + K.no_big(2, 4))
write("xcyc6", build_cyclic(6).cls)
