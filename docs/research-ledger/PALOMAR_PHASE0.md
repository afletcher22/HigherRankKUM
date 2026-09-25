# Palomar Phase 0: certification feasibility

Date: 2026-09-25.

Branches:

* `rank4-heavy-flat-splice-research`: measurement and conversion tooling
  (`experiments/rank4_heavy_flat_splice/`);
* `probe/lrat-kernel`: Lean probes of kernel-checked certificates and the encoding layer;
* `probe/toolchain-v4.35`: the build on the Palomar-eligible toolchain.

The probe branches are measurement-only. Nothing on them is part of the trusted Lean graph.

## 1. Palomar constraints that drive the plan

Palomar (palomar-registry.org; Lean FRO + ICARM) accepts a submission only if all of the following
hold:

* **Axioms.** The solution uses only `propext`, `Classical.choice` and `Quot.sound`.
  `Lean.ofReduceBool` is rejected, so neither `native_decide` nor `bv_decide` can be used.
* **Independent replay.** Every proof is replayed by the NanoDa kernel.
* **Resources.** The runner has 16 cores and 32 GB, with an execution budget of 19,800 s.
* **Toolchain.** The floor is Lean `v4.35.0-rc2` (`PalomarSubmission/toolchains.json`).
* **Challenge file.** It imports only Lean core and Mathlib (or Tau Ceti), and is at most 1,000
  lines and 100 KiB.

Every SAT claim on the rank-4 critical path must therefore either be replaced by a human proof,
or enter Lean as a certificate checked by the kernel itself, together with a Lean proof that the
SAT encoding is sound.

## 2. Certificate sizes (all nine critical-path claims)

Formulas come from `certify.formula`, and the X/X' claims use the block encoding (`w=6`). The
solver is CaDiCaL 1.9.5 via pysat. The pipeline is:

* `cert_measure.py` solves each claim and streams the DRUP proof to disk;
* `lrat_emit.py` converts it to trimmed LRAT (RUP hints only);
* `lrat_core.py` restricts the formula to the clauses the proof uses;
* `lrat_check.py` is an independent strict LRAT checker.

Every certificate listed below as converted was re-checked with it.

| Claim | Clauses | DRUP lemmas | LRAT steps | LRAT hints | Core clauses | Verdict |
|---|---|---|---|---|---|---|
| KUM, n=6 (`kum6`) | 2,692 | 337 | 81 | 682 | 221 | fits |
| KUM, n=8 (`kum8`) | 18,020 | 14,442 | 10,346 | 371,427 | 6,242 | fits (measured) |
| X', N=8 (`cyc8`) | 337,649 | 79,464 | 10,140 | 341,624 | 10,361 | fits (measured) |
| X', N=10 (`cyc10`) | 502,511 | 119,133 | 12,003 | 376,147 | 13,291 | fits (estimate) |
| X', N=12 (`cyc12`) | 620,609 | 133,673 | 13,162 | 445,181 | 14,723 | fits (estimate) |
| X, L=14 (`lin14`) | 488,752 | 118,920 | 11,370 | 358,342 | 11,706 | fits (estimate) |
| KUM, n=10 (`kum10`) | 267,700 | 951,423 | — | — | — | too large (17.8M lemma literals) |
| hitting lemma, n=14, 9-plane | 2,349,956 | 2,090,419 | — | — | — | too large (25.1M lemma literals) |
| hitting lemma, n=14, 6-line | 2,351,958 | 428,858 | — | — | — | not converted; likely too large |

Additional measurement:

* **Strict t=0 part of KUM at n=10 (`kum10s`).** This is the only part of n=10 not already covered
  by the Lean tight-set and dangerous-hyperplane reductions. It has 268,192 clauses and 297,732
  DRUP lemmas (4.7M lemma literals), about a third of the full n=10 proof. Its LRAT size is
  pending.

SAT base lemmas for Theorems G and L4, which replace the n=14 hitting SAT at k=3 (decision of
2026-09-25):

| Claim | Clauses | DRUP lemmas | LRAT steps | LRAT hints | Core clauses | Verdict |
|---|---|---|---|---|---|---|
| L4 base: 4-point line, n0=10 (`baseL4`) | 259,074 | 64,906 | 27,023 | 826,338 | 27,073 | at the ceiling; needs a case split or a smaller proof |
| G base: 6-point plane, n0=10 (`baseG`, all r(C)) | 138,106 | 159,158 | pending | | | |

The core is small. The proofs use only 3% of the X' formula's clauses, and a third of KUM(8)'s.
Re-solving the core shrinks the proof modestly and inconsistently: KUM(8) went from 371k to 293k
hints, and X'(8) from 342k to 237k.

## 3. Kernel cost of `from_lrat` (GitHub runner, 4 vCPU / 16 GB)

| Probe | Clauses | Hints | Tactic | Kernel | Build | Peak RSS | `leanchecker` replay |
|---|---|---|---|---|---|---|---|
| `Kum6` | 2,692 | 682 | 0.4 s | 0.3 s | 2 s | 1.1 GB | 7 s |
| `Kum8` (full formula) | 18,020 | 371k | 148 s | 120 s | 3:24 | 13.4 GB | 1:48, 12.5 GB |
| `Kum8Core` | 5,878 | 293k | 121 s | 99 s | 2:41 | 10.7 GB | 1:32, 10.1 GB |
| `Cyc8Core` | 6,922 | 237k | 83 s | 65 s | 1:55 | 8.6 GB | 1:11, 8.0 GB |

Every probe theorem depends only on `[propext, Classical.choice, Quot.sound]`.

**Cost model.** Memory scales with the proof, not the formula: about **36 KB of RSS per LRAT
hint**, and about **0.3 ms of kernel time per hint**. On Palomar's 32 GB runner, this caps one
certificate module at roughly **800k hints**, and modules this heavy must not be built in
parallel.

Consequences:

* The six small claims (KUM 6/8, X' N=8/10/12, X L=14) can be kernel-checked. They total about
  2.1M hints; built one after another, that is roughly 20–25 minutes of tactic, kernel and replay
  time.
* KUM(10) and the two n=14 hitting cases cannot be checked as they stand.

## 4. The encoding layer

A certificate proves a propositional fact. The link to matroids needs a Lean proof that any
matroid counterexample would satisfy the formula. The design, in `probe/lrat-kernel`
(`probes/Probe/Enc*.lean`), has four parts:

* **`lrat_refutation foo cnf lrat`.** It calls Mathlib's `fromLRATAux` and stores the core formula
  as data (`foo.fmla : Sat.Fmla`) with `foo.refute : Sat.Fmla.proof foo.fmla []`. It skips the
  propositional statement that `lrat_proof` also builds.
* **`clause_witnesses`.** It stores one witness per core clause, exported by `lean_witness.py`.
  Each witness names the rule that produced the clause: order, cap, density, monotone, unit
  increase, local submodularity, or a cyclic-order window.
* **Kernel-only checks.** `fmlaBEq` checks that the stored formula is exactly the one regenerated
  from the witnesses, and `valid` checks each witness's side conditions. Both run under
  `decide +kernel`, which adds no axioms.
* **`RankModel N`.** An abstract rank function on bitmasks with exactly the properties the clauses
  use. `gen_sound` shows that every valid witness yields a clause satisfied by `r(X) ≥ v`.
  Therefore `no_model` shows that no rank model exists, whenever a refutation is available.

The bridge (`probes/Probe/EncBridge.lean`, branch `probe/encoding`, on the `v4.35.0-rc3`
toolchain) turns a counterexample matroid into a `RankModel`, which the certificate then rules out:

* number the ground set, and read a bitmask `X` as `maskSet σ X`;
* take `r X = (M.eRk (maskSet σ X)).toNat`;
* derive each rank-model property from a Mathlib lemma: `eRk_le_encard`, uniform density,
  `eRk_mono`, `eRk_insert_le_add_one` and `eRk_inter_add_eRk_union_le`;
* turn every cyclic list into a numbering `Fin N ≃ M.E` whose windows are the list's windows.

**End-to-end result:**
`Probe.Enc.Kum6.solves : HigherRankKUM.SolvesKUMAtRankSize α 4 6`. It is rank-4 KUM on 6
elements, stated in the repository's own solver interface, and depends only on
`[propext, Classical.choice, Quot.sound]`.

**Status: working end to end for n=6** (the refutation-to-rank-model part; the full matroid
theorem is below). `Probe.Enc.Kum6.no_rank_model : RankModel 6 → False`
builds and depends only on `[propext, Quot.sound]`. The whole path from the LRAT certificate to
"no abstract rank model exists" is kernel-checked.

Measured cost of the data layer:

| Module | Refutation | Witness validity | Formula equality | Build | Peak RSS | Replay |
|---|---|---|---|---|---|---|
| `EncKum6` (221 clauses) | 0.10 s | 0.24 s | 0.52 s | 1.2 s | 1.1 GB | 8 s |
| `EncKum8` (6,242 clauses) | 155 s | 166 s | 200 s | 5:13 | 13.2 GB | 3:19, 12.6 GB |

The kernel-only checks roughly triple the kernel time at n=8, but peak memory stays at the
refutation's level. It is still affordable, and it is the obvious optimization target, since
`decide +kernel` evaluates the structurally recursive `fmlaBEq` and `valid` slowly.

## 5. Toolchain

* The repository was pinned to `v4.33.0-rc2`, below Palomar's floor.
* `probe/toolchain-v4.35` builds the **whole project (3,266 jobs), including the vendored
  Rank3KUM, on Lean and Mathlib `v4.35.0-rc3`**. The only change needed is the Mathlib rename
  `Equiv.setCongr` → `Set.equivOfEq` (and `Equiv.setCongr_apply` → `Set.equivOfEq_apply`).
* That rename touches 21 sites: 8 in HigherRankKUM and 13 in `vendor/Rank3KUM`.
* The vendored snapshot is byte-for-byte locked (SHA256SUMS in CI). Adopting the upgrade needs a
  policy decision: patch the vendored copy and record the diff, or update Rank3KUM upstream and
  re-vendor it.

The draft `Challenge.lean` (`probes/Probe/ChallengeDraft.lean`) states rank-4 KUM using Mathlib
only, and it compiles.

## 6. What this changes in the plan

1. **Replace the three oversized SAT claims.**
   * *n=14 hitting cases:* push Lemma U's counting down to k=3. That removes both claims.
   * *KUM(10):* only the strict t=0 part needs SAT. If its certificate is still too large, split it
     further or find a structural proof.
2. **Keep the small claims as certificates** unless a human proof of Theorem X arrives. That proof
   remains the research priority because of rank 5, not because of certification cost.
3. **Adopt the v4.35 toolchain early**, once the vendoring policy is decided.
4. **Build the matroid-to-`RankModel` bridge**, then do the same for the block encoding of X/X'.
   Those formulas should be re-emitted with the arithmetic variable numbering `4X+v`, which the
   witness layer decodes.
