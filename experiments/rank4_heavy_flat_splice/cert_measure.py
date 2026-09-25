"""Measure the certification cost of the SAT claims on the rank-4 critical path.

For each claim: build the formula (certify.formula), write it as DIMACS, solve with CaDiCaL and
proof output, copy the solver's binary DRAT proof to disk without expanding it in memory, and
record sizes.  With 'check', also expand the proof to text and run drup_check on it (only
sensible for moderate proofs).  Output files go to certs/ (gitignored); one JSON line per claim
is appended to certs/measure.jsonl.

Usage: python cert_measure.py [check] NAME...
NAMEs as in certify.py: cyc8 cyc10 cyc12 lin14 kum6 kum8 kum10 hit14plane hit14line.  Any other
NAME re-solves the existing certs/NAME.cnf (for example a core written by lrat_core.py).
"""
import json, os, shutil, sys, time
import pysat.solvers as PS
from certify import formula, _flush_c_streams
from drup_check import check

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "certs")


def binary_drat(path):
    """Stream a binary DRAT file, yielding (is_deletion, literals)."""
    with open(path, "rb") as f:
        data = f.read(1 << 20)
        pos, lits, kind, acc, shift = 0, [], None, 0, 0
        while data:
            for b in data:
                if kind is None:
                    kind = b
                    continue
                acc |= (b & 0x7F) << shift
                if b & 0x80:
                    shift += 7
                    continue
                if acc == 0:
                    yield kind == 0x64, lits
                    lits, kind = [], None
                else:
                    lits.append(-(acc >> 1) if acc & 1 else acc >> 1)
                acc, shift = 0, 0
            data = f.read(1 << 20)


def text_lines(path):
    return [("d " if d else "") + " ".join(map(str, lits + [0])) for d, lits in binary_drat(path)]


def write_dimacs(path, cls):
    nv = max(abs(l) for c in cls for l in c)
    with open(path, "w") as f:
        f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    return nv


def measure(name, do_check):
    os.makedirs(OUT, exist_ok=True)
    t0 = time.time()
    cnf_path = os.path.join(OUT, f"{name}.cnf")
    try:
        cls = formula(name)
    except ValueError:
        # not a named claim: re-solve an existing CNF, e.g. a core from lrat_core.py
        from lrat_emit import read_dimacs
        cls = read_dimacs(cnf_path)
    nv = write_dimacs(cnf_path, cls)
    rec = {"name": name, "solver": "Cadical195", "vars": nv, "clauses": len(cls),
           "literals": sum(len(c) for c in cls), "cnf_bytes": os.path.getsize(cnf_path),
           "build_s": round(time.time() - t0, 1)}
    t1 = time.time()
    s = PS.Cadical195(bootstrap_with=cls, with_proof=True)
    res = s.solve()
    _flush_c_streams()
    rec["solve_s"] = round(time.time() - t1, 1)
    rec["result"] = "SAT" if res else "UNSAT"
    if not res:
        proof_path = os.path.join(OUT, f"{name}.drat.bin")
        s.prfile.seek(0)
        with open(proof_path, "wb") as f:
            shutil.copyfileobj(s.prfile, f)
        rec["proof_bin_bytes"] = os.path.getsize(proof_path)
        adds = dels = add_lits = 0
        for d, lits in binary_drat(proof_path):
            if d:
                dels += 1
            else:
                adds += 1
                add_lits += len(lits)
        rec["lemmas"], rec["deletions"], rec["lemma_literals"] = adds, dels, add_lits
        if do_check:
            t2 = time.time()
            ok, msg = check(cls, text_lines(proof_path))
            rec["check"] = ("VERIFIED: " if ok else "REJECTED: ") + msg
            rec["check_s"] = round(time.time() - t2, 1)
    s.delete()
    print(json.dumps(rec), flush=True)
    with open(os.path.join(OUT, "measure.jsonl"), "a") as f:
        f.write(json.dumps(rec) + "\n")


if __name__ == "__main__":
    args = sys.argv[1:]
    do_check = bool(args) and args[0] == "check"
    if do_check:
        args.pop(0)
    for nm in args:
        measure(nm, do_check)
