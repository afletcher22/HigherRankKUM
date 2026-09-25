# Independent re-implementation of the extension-theorem SAT checks

Written from the mathematical specification alone, without reading or importing the other scripts
in this folder, as a cross-check of `local_sat.py` and `cyclic_sat.py`. See
`docs/research-ledger/RANK4_EXTENSION_THEOREM.md` §2.4.

* **E1** (`cnf_enc.exact_cnf`) is an exact encoding. There is one variable for each subset of size
  1–4, with hereditary clauses and single-step augmentation, so its models are exactly the rank-4
  matroids. Its SAT models are genuine counterexamples.
* **E2** (`cnf_enc.block_cnf`) is a sound relaxation. It imposes rank axioms on the blocks
  `S ∪ {4 consecutive e's}`.
* `common.py` enumerates the interleavings with two independent generators, which must agree, and
  checks the count against the closed formula.

| Script | What it does |
|---|---|
| `run.py {A\|B} P {exact\|block} [solver]` | One instance: A is the linear form (L=P), B the cyclic form (N=P) |
| `verify.py models/*.pkl` | Rebuilds the full rank function of a SAT model and checks the axioms and the counterexample property by brute force (needs numpy) |
| `controls.py` | Positive controls (a known binary counterexample, random GF(p) matroids, U_{4,18}) and negative controls (three non-matroids) |
| `log_*.txt` | Output of the runs reported in the ledger |
