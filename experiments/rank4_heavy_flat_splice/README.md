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

## Scripts from the earlier session: `bsi/`

`bsi/block_exhaust.py M` exhaustively lists the cyclic orders of `M\D`, with `D={1,2,4,8}`, into
which `D` cannot be inserted contiguously at any gap. It is binary only. `bsi/block_bin.py` is its
helper module. These are the natural starting point for the light-class falsification task in §6
of the ledger note.
