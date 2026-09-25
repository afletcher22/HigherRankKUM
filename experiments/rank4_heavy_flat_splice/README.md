# Heavy-flat splice and 3k-plane completion experiments

Supporting scripts for `docs/research-ledger/RANK4_HEAVY_FLAT_SPLICE.md`. These are finite
computations only; they are outside the trusted Lean graph and are not wired into CI.

Run each script from this directory with Python 3; `orbits.py` also needs numpy. Random stress
scripts take a seed as their first argument.

## Library modules

| File | Contents |
|---|---|
| `kum.py` | Rank-oracle matroids over GF(2), GF(p) and sparse paving; flat profiles; strict/t classification; constrained CBO search |
| `bin_class.py` | Enumeration of binary multisets under flat caps, using PG(3,2) lines and planes |
| `gen.py` | Random GF(p) instances containing a prescribed 3k-plane |
| `gtest.py` | Schedules for 3k-plane gluing, and "does a given K-order extend?" |
| `ctest.py` | Completion keeping the K-order inherited from a deletion CBO |
| `bsl.py` | Heavy-flat splice for planes (rho=3), plus a uniform-density check |
| `hfs.py` | Heavy-flat splice for all ranks rho=1,2,3 (Theorem 4) |
| `hitting.py` | Hitting-lemma search for heavy flats |

## Certificates and stress runs

| Script | What it checks |
|---|---|
| `orbits.py 10 2` | Exact n=10 strict t=0 binary class: 28,476 patterns, 16 orbits. Writes `orbits_n10_t0.json`, which is committed. |
| `run_g_n10.py` | Schedules for 3k-plane gluing on every 6-plane of the 16 orbits |
| `run_c_n10.py` | Inherited-order completion for all 153,232 k=2 cases |
| `verify_fail1.py` | Binary k=3 completion counterexample, by exhaustive CBO enumeration (~1.5 min) |
| `verify_fail2.py` | GF(3) k=3 completion counterexample, by exhaustive CBO enumeration (~1 min) |
| `k4_mech.py` | Targeted k=4 completion failures |
| `orbit8.py`, `orbit8b.py` | Perfect-core counterexample with `M(K4)` |
| `run_c_rand.py SEED K NINST NSIG` | Random completion stress |
| `run_g_rank.py` | Perfect-core extendability split by the rank of the complement |
| `run_switch.py` | Whether some 3k-plane has a complement of rank >=3 |
| `run_bsl.py SEED` | Hitting search plus plane splice, verified end to end |
| `run_hfs.py SEED` | Point and line splices, verified end to end |
| `run_hit.py SEED` | Hitting lemma for heavy flats at k=4..10 |
| `run_light.py SEED` | Contiguous basis splice on light matroids and on the k=6,7 witnesses |

## Decomposition principle and Theorem G (ledger §7)

The SAT scripts need the `python-sat` package (`pip install python-sat`).

| Script | What it does |
|---|---|
| `dp.py` | Site detection, site-CBO search, iterated plane splicing, and Edmonds partitions in rank 3 |
| `run_dp.py SEED` | Base search plus DP construction on the n=10 class, the counterexamples, the witnesses and random k=3..5 |
| `run_base_k2.py SEED N` | k=2 base lemma stress over GF(3), GF(5) and GF(7) |
| `run_base_tau.py`, `base_shapes.py`, `run_shapes.py` | Perfect-core extendability to a site-CBO, split by rank of complement and by skeleton |
| `b2_exhaustive.py` | Exhaustive, representation-free proof of the base lemma for `r(C)=2` |
| `base_sat.py [rC]` | **SAT proof of the 10-element base lemma** for a 6-point plane (UNSAT for `rC=2,3,4`) |
| `base_sat_sanity.py`, `base_sat_controls.py` | Sanity checks and discriminating controls for the SAT encoding |
| `base_sat_general.py RHO F` | 10-element base lemmas for other flats: `3 7`, `1 2` and `2 4` are UNSAT; `3 5` and `2 3` are SAT |
| `theorem_g.py`, `run_theorem_g.py SEED` | Theorem G pipeline with the paper choice lemma, verified end to end |
| `theorem_pl.py`, `run_theorem_pl.py SEED` | Pipelines for k-points and 2k-lines, with the base chosen by search |

## Remaining flat types, n=10, and the light regime (ledger §8–9)

| Script | What it does |
|---|---|
| `analyze_sat_cx.py`, `base_sat_minimal.py` | Inspect the 10-element base counterexamples, and find the minimal base conditions (strictness) under which the lemmas hold |
| `kum_4_10_sat.py [strict]` | **Direct SAT proof of rank-4 KUM on 10 elements**, UNSAT with and without `strict` |
| `choice_general.py`, `run_choice_general.py SEED` | Base choice by search, plus the full construction, for k-points, 2k-lines, (2k-1)-lines and (3k-1)-planes (159/159) |
| `light_block.py`, `run_light_block.py SEED` | Exhaustive DFS for fully blocked contiguous insertions in light GF(3)/GF(5) matroids |
| `run_U_binary.py` | Exact binary test of Conjecture U at n=14 and n=18. It finds 12 light blocked matroids at n=18 |
| `run_U_basis_rule.py` | Classifies every basis of the light blocked matroids. It uses `blocked_n18.json`, the exhaustive list of the 360 blocked binary matroids at n=18 |
| `run_U_minimal.py SEED` | Blocked-insertion search for matroids that are light except for one heavy feature |
| `analyze_light_block.py` | Gap-by-gap anatomy of a light blocked insertion (binary n=18) |
| `tetra_family.py SEED N` | Tetrahedral light families over GF(2) and GF(3), testing the basis-selection rules R1 and R2 on every basis type |
| `base_cegar.py RHO F CAPS` | Lazy-clause SAT for base lemmas on 14 elements. The 8-point-plane run was stopped undecided |
| `cegar_check10.py` | Validates `base_cegar.py` against the known 10-element results |

## Scripts from the earlier session: `bsi/`

`bsi/block_exhaust.py M` exhaustively lists the cyclic orders of `M\D`, with `D={1,2,4,8}`, into
which `D` cannot be inserted contiguously at any gap. It is binary only. `bsi/block_bin.py` is its
helper module. These are the natural starting point for the light-class falsification task in §6
of the ledger note.

## Extension theorem and the reduction of rank-4 KUM (`RANK4_EXTENSION_THEOREM.md`)

| Script | What it does |
|---|---|
| `ext.py` | Non-contiguous extension of a deletion CBO by a basis (memoised DFS) |
| `nonext.py` | Adversarial search for deletion CBOs with no extension, with interior-extension pruning |
| `ext_crosscheck.py` | Validates `ext.extend` and `nonext.py` against brute-force CBO enumeration (n=10) |
| `ext_blocked.py`, `ext_blocked18.py` | Every fully blocked binary order at n=14 and n=18 extends; lists the shapes used |
| `ext_bin_exhaust.py M [strict]` | Exhaustive binary check of the extension theorem (non-extendable CBOs exist only at n=10, with t=3) |
| `ext_local_bin.py`, `ext_local_verify.py` | Exact binary threshold 14 for the local form, plus an independent brute-force check |
| `local_sat.py L` | **SAT proof of the local form (Theorem X)**: SAT for L<=13, UNSAT for L=14 |
| `cyclic_sat.py N [block\|full]` | **SAT proof of the cyclic form (Theorem X')**: SAT for N=6, UNSAT for N=7..14 |
| `local_sat_controls.py`, `cyclic_sat_controls.py`, `cyclic_sat_more.py` | Thresholds, second and third solvers, full-rank-function encoding, real-matroid consistency |
| `run_nonext_real.py SEED N` | Adversarial non-extension search on GF(3)/GF(5)/GF(7) and sparse paving matroids |
| `kum_small_sat.py N [nodensity]` | Direct SAT proof of rank-4 KUM on N<=9 elements (used for N=6 and 8), with a no-density control |
| `lemma_h.py` | Runs the Lemma H construction from every adversarial starting basis and asserts each step |
| `hit_general.py` | Random evidence for a unified hitting lemma, with 3k-planes and 2k-lines present |
