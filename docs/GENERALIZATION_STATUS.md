# Generalization Status

Accurate as of 2026-09-27. This file separates certified generic infrastructure from rank-specific
results and open research targets. For each result it records where the Lean proof lives and how it
is proved. Where `docs/RANK4_COVERAGE.md` (which predates van den Heuvel–Thomassé and the rank-4
proof) disagrees with this file, this file is current.

## Status vocabulary

- **Formalized generic**: the Lean theorem has no fixed ambient-rank hypothesis and lives in the
  HigherRankKUM generic dependency chain.
- **Formalized internal**: the result is proved in Lean inside this repository (including the
  frozen local Rank3KUM snapshot), with no live external proof dependency.
- **Formalized conditional**: Lean verifies the reduction, but an explicitly stated solver or
  literature theorem remains a hypothesis.
- **Computational evidence**: an exact finite computation (a SAT/UNSAT run, or an LRAT proof checked
  outside Lean). It is not a Lean theorem.
- **Research target**: no proof is currently present in HigherRankKUM.

Each formalized result is also labelled by location and by method.

- **Where.**
  - *main*: the library `HigherRankKUM/` on branch `rank4-heavy-flat-splice-research`. Its last
    Lean change is commit 541bafa, and the Lean CI run on it (36197710010) is green.
  - *probe/rank4*: modules under `probes/Probe/` on branch `probe/rank4` (local worktree
    `../probe-worktree`). They import the main library but are not part of it. Only the
    `probe.yml` workflow builds them.
- **How.**
  - *Human*: an ordinary Lean proof.
  - *Certificate*: a kernel-checked SAT certificate. It has three parts:
    - an LRAT refutation of a CNF formula, checked by the Lean kernel (no `native_decide`, no
      `ofReduceBool`);
    - kernel-checked witnesses showing that the formula is exactly the intended encoding;
    - a Lean proof that any matroid counterexample would give a model of that formula.

    Hint counts are the LRAT hints of the certificate actually checked in Lean
    (`probes/data/*.lrat`).

Every theorem named below depends only on `propext`, `Classical.choice` and `Quot.sound`, the
Palomar axiom set.

## At a glance

| Rank | Result | Status | Where | How |
|---|---|---|---|---|
| any | vHT Theorem 2.1; coprime KUM; Edmonds partition; double covers | formalized generic | main | human |
| prime `p` | divisible KUM at `p` implies full KUM at `p` | formalized generic | main | human |
| 1 | divisible KUM | formalized internal | main | human |
| 2 | divisible KUM, and KUM at odd sizes | formalized internal | main | human |
| 3 | full KUM | formalized internal | main | human (vendored Rank3KUM plus vHT) |
| 4 | full KUM | formalized internal | probe/rank4 | human plus 7 certificates (2.17M hints) |
| 4 | pair-chain insertion XP (would replace X′) | human reduction plus SAT; Lean work not started | ledger; `probe/xp` | 4 local lemmas, about 80k hints |
| 5 | KUM(5,10) | literature (SAT) and our own SAT run | none | computational evidence |
| 5 | KUM(5,5k) for `k ≥ 3` | research target | none | none |
| general | divisible KUM (and intermediate gcds at composite ranks) | research target | none | none |

## Formalized generic infrastructure (main)

HigherRankKUM contains arbitrary-rank formalizations of:

- integer uniform density `UniformlyDense` and tightness `Tight`;
- rational/cross-multiplied density `UniformlyDenseRatio` and `TightRatio`;
- restriction and tight-contraction density inheritance;
- tight sets as flats under the relevant finite positive-density hypotheses;
- looplessness from positive density;
- `cyclicIndex`, cyclic windows, and arbitrary-rank `CyclicBasisOrder`;
- contraction rank bookkeeping and basis lifting;
- abstract restriction/contraction gluing;
- balanced integer interleaving and periodic rational interleaving;
- `SolvesDivisibleKUMAtRank`, `SolvesKUMAtRankSize`, `SolvesKUMAtRank`, and lower-rank solver
  interfaces;
- generic divisible and rational proper-tight reductions.

**van den Heuvel–Thomassé** (arXiv:0912.2929, JCTB 2012), in `HigherRankKUM/VHT/`. All proofs are
human.

- **Theorem 2.1**, direction (b) ⇒ (a): `HigherRankKUM.VHT.theorem_2_1 : VHT.Statement α`
  (`Theorem21.lean`). Let `M` be finite and loopless, `ω` a weight function and `D > 0`. If
  `ω(A) ≤ D·r(A)` for every `A`, then some `φ : E → ℤ/D` makes every arc set `E_φ(x)` independent.
  The paper's fairness argument (an ordered push sequence) is replaced by a sink component of the
  push graph; see `docs/research-ledger/VHT_FORMALIZATION_PLAN.md`.
- **Coprime KUM at every rank** (vHT Theorem 3.1):
  `VHT.solvesKUMAtRankSize_of_coprime : Nat.Coprime r m → SolvesKUMAtRankSize α r m`.
- **Edmonds partition** `VHT.edmonds_partition` (weight 1: `k` disjoint bases covering `E` when
  `|E| = k·r`) and **double covers** `VHT.double_cover` (weight 2 on `ℤ/(2k+1)`: `2k+1` bases with
  every element in exactly two). Both are in `Covers.lean`. They take `VHT.Statement α` as an
  argument and are applied to `VHT.theorem_2_1`.

**Prime-rank reduction.**
`solvesKUMAtRank_of_prime : p.Prime → SolvesDivisibleKUMAtRank α p → SolvesKUMAtRank α p`
(`HigherRankKUM/PrimeRank.lean`). At a prime rank every size is either coprime to `p` (vHT) or
divisible by `p`.

The rational layer was added without replacing the older divisible interface. In reduced density
ratio `p/q`, tight-set ranks factor by `q`, and the periodic scheduler glues restriction/contraction
cyclic orders at the original density.

## Low-rank bases (main)

- **Rank 1.** Divisible KUM, formalized internally (`solvesDivisibleKUMAtRank_one`).
- **Rank 2.**
  - Divisible KUM uses the native HalfWeave-style proof (`solvesDivisibleKUMAtRank_two`).
  - Odd sizes follow from coprime KUM (`solvesKUMAtRankSize_two_odd`).
  - Together these cover every size. They are not yet packaged as a single
    `SolvesKUMAtRank α 2`, which would be one line via `solvesKUMAtRank_of_prime`.
- **Rank 3.** Full KUM, `solvesKUMAtRank_three : SolvesKUMAtRank α 3` (`PrimeRank.lean`).
  - It combines the vendored divisible theorem (`solvesDivisibleKUMAtRank_three`, adapter
    `HigherRankKUM/LowRank/RankThree.lean`) with coprime KUM.
  - `vendor/Rank3KUM/` is a snapshot of Rank3KUM version-3 commit
    `eff642a2e01fac4fc1f6f76e592eeea46c3152c9`. Its only changes are the Lean/Mathlib
    v4.35.0-rc3 toolchain patches recorded in `vendor/Rank3KUM/PATCHES.md`.

The earlier statement that HigherRankKUM has no formalization of the van den Heuvel–Thomassé
coprime theorem, so that odd-size rank-2 instances appear as explicit hypotheses, is **obsolete**.
No axiom and no live external Rank3KUM dependency is used.

## Rank 4: full KUM, kernel-checked on `probe/rank4`

**Theorem.** `HigherRankKUM.solvesKUMAtRank_four : SolvesKUMAtRank α 4`
(`probes/Probe/Rank4/Final.lean`): every finite uniformly dense rank-4 matroid has a cyclic basis
ordering. It depends on the axioms `[propext, Classical.choice, Quot.sound]` only.

**Verification.** Workflow "Palomar kernel probe", run 36223257829, on commit a4ead33 (the head of
`probe/rank4`), 2026-09-26: success.

- The run builds the heavy certificate modules one at a time, then `Probe.Rank4.Final`.
- It replays `Probe.Rank4.Final` with `leanchecker`, and fails if `ofReduceBool`, `sorryAx` or
  `trustCompiler` appears.
- Resources on the GitHub runner (4 vCPU, 16 GB):
  - wall time 33 minutes;
  - slowest module `Hit14Line`, 11 minutes;
  - peak memory 12.8 GB, for `ExtCyc12`.
- For comparison, the Palomar runner has 16 cores, 32 GB and a budget of 19,800 s.

### Proof structure

The proof is a strong induction on `n = |E|` (`solvesKUMAtRank_four_of_hitting`,
`probes/Probe/Rank4/Full.lean`).

| `n` | Argument | Where | How |
|---|---|---|---|
| odd | coprime KUM (vHT) | main | human |
| 4 | the ground set is a basis | probe/rank4 | human |
| `4k`, `k ≥ 2` | **Theorem D**: Edmonds splits `E` into `k` bases (vHT); delete one basis; order the rest by induction; reinsert with X′(`4k−4`). Base case KUM(4,8). | probe/rank4: `Rank4/TheoremD.lean`, `TheoremDCert.lean`, `ExtFinal.lean` | human, given X′ |
| 6 | duality with rank-2 KUM (`Rank4.exists_cyclicBasisOrder_of_rank_four_six`) | main: `Rank4/SixElementBoundary.lean` | human |
| 8 | Kotlar–Ziv: two disjoint bases of a rank-4 matroid have a full serial symmetric exchange (`KotlarZiv.serial_exchange_rank_four`, `solvesKUMAtRankSize_four_eight`) | probe/rank4: `Rank4/SerialExchange.lean`, `Rank4/Kum8.lean` | human |
| 10 | vHT with weight 2 on `ℤ/5` has fibres of size 2, so `E` is a chain of five pairs with every `P_i ∪ P_{i+1}` a basis. Certificate `chain10`: some orientation of the chain, or of a chain re-split at one window, is a CBO (`solvesKUMAtRankSize_four_ten_of_pairChain`). | probe/rank4: `Chain10.lean`, `Rank4/Kum10Chain.lean` | human plus certificate (14,738 hints) |
| `4k+2`, `k ≥ 3`, with a nonempty proper tight set | rational tight reduction; its rank-2 input at odd size `2k+1` comes from coprime KUM (`exists_cyclicBasisOrder_of_rank_four_gcd_two_of_nonempty_proper_tight'`) | main: `Rank4/Unconditional.lean` | human |
| `4k+2`, `k ≥ 3`, strict, with a dangerous plane | dangerous-hyperplane schedule; its rank-3 input comes from `solvesKUMAtRank_three` (`Rank4DangerousBranches.exists_cbo_of_dangerous_hyperplane'`) | main: `Rank4/Unconditional.lean` | human |
| `4k+2`, `k ≥ 3`, strict, `t = 0` | the hitting lemma gives a basis `S` with `M∖S` uniformly dense on `4k−2` elements; induction orders `M∖S`; X′(`4k−2`) reinserts `S` | probe/rank4: `Rank4/Full.lean` | human, given the hitting lemma and X′ |

With these, the tight/dangerous gcd-two reductions of the main library are **no longer
conditional**: their odd rank-2 and rank-3 inputs are discharged by coprime KUM and full rank-3
KUM.

**The hitting lemma** (`hittingLemma`, `Final.lean`) covers strict `t = 0` matroids on `4k+2`
elements, `k ≥ 3`. The interface (`StrictT0`, `Deletable`, `MeetsDemands`) is in
`Rank4/Hitting.lean`.

- `k ≥ 4`: Lemma U applied to a vHT double cover (`Hitting.lemmaU`, `Rank4/LemmaU.lean`;
  `hitting_ge_four`, `Rank4/HitGeFour.lean`). Human.
- `k = 3`, split by the heavy flat present:

  | heavy flat | proof |
  |---|---|
  | no 9-element plane and no 6-element line | Lemma H (`Hitting.lemmaH`, `Rank4/LemmaH.lean`); human, valid for every `k ≥ 2` |
  | a 9-element plane | certificate `hit14g` (`Hit14G.lean`) |
  | a 6-element line and no 9-element plane | certificate `hit14line` (`Hit14Line.lean`) |

**The extension theorem X′.** `Rank4Extension α N` (`Rank4/TheoremD.lean`) states: if `S` is a
basis of a rank-4 matroid `M`, and `M∖S` (on `N` elements) has a CBO, then `M` has a CBO. There is
no density hypothesis. It is proved in `ExtFinal.lean`:

- `N = 8, 10, 12`: the cyclic certificates `xcyc8`, `xcyc10` and `xcyc12`;
- `N ≥ 14`: the linear lemma X on 14 consecutive entries (certificate `xlin14`), plus a human
  bridge (`rank4Extension_of_linCert`, `ExtBridge.lean`) that interleaves `S` into one stretch of
  14 entries.

Theorem D uses X′ at `N = 8, 12` and `N ≥ 16`. The `4k+2` step uses it at `N = 10` and at
`N ≥ 14`.

### Certificates on the critical path

| Certificate | Claim | LRAT hints | Lean module (probe/rank4) |
|---|---|---|---|
| `chain10` | KUM(4,10) from a 5-pair chain | 14,738 | `Chain10.lean` |
| `xcyc8` | X′(8) | 254,213 | `ExtCyc8.lean` |
| `xcyc10` | X′(10) | 300,537 | `ExtCyc10.lean` |
| `xcyc12` | X′(12) | 390,228 | `ExtCyc12.lean` |
| `xlin14` | X, linear, length 14 | 311,065 | `ExtLin14.lean` |
| `hit14g` | hitting lemma, `k = 3`, 9-element plane | 55,754 | `Hit14G.lean` |
| `hit14line` | hitting lemma, `k = 3`, 6-element line | 842,574 | `Hit14Line.lean` |
| **total** | | **2,169,109** | |

Two corrections to figures quoted in the ledger:

- The Lean-checked `hit14line` has 842,574 hints. The figure of 623,520 was a native-CaDiCaL
  measurement of a different encoding of the same claim, not the certificate in Lean.
- The four X′ certificates total about 1.26M hints, not about 800k.

**Superseded certificates.** These are still on the probe branches but no longer imported by
`Final.lean`:

- KUM(4,6): `kum6`, 682 hints (`probe/encoding`), replaced by duality;
- KUM(4,8): `kum8`, 371,427 hints, replaced by Kotlar–Ziv;
- the five KUM(4,10) certificates `baseG2`, `baseG3`, `baseG4`, `baseL4` and `kum10l`, 2.27M
  hints in total, replaced by `chain10`.

### Migration and Palomar packaging (in progress)

- **Not migrated.** The rank-4 proof exists only on `probe/rank4`.
  - The main library holds only part of the human input: vHT and its covers, KUM(4,6), and the
    tight and dangerous-plane reductions.
  - The following are probe-only: Theorem D, Kotlar–Ziv, the hitting-lemma interface, Lemma H,
    Lemma U, the SAT encoding layer, all certificates, and the assembly.
- **Migration script.** A draft script, `migrate.py`, exists in a working scratchpad and is not
  committed. It sends:
  - the SAT layer to `HigherRankKUM/SAT/`;
  - the paper lemmas to `HigherRankKUM/Rank4/`;
  - the certificate modules, their data and the assembly to a separate library
    `HigherRankKUMCert`, which is not built by default.

  Its module list predates the Kotlar–Ziv, `chain10` and `HitGeFour` changes, so it needs
  updating.
- **Palomar packaging.**
  - The toolchain (Lean/Mathlib v4.35.0-rc3) is above Palomar's floor.
  - A draft `Challenge.lean` stating rank-4 KUM with Mathlib only compiles. It is at
    `probes/Probe/ChallengeDraft.lean` on `probe/lrat-kernel` and `probe/encoding`.
  - Still missing: `Solution.lean`, `comparator.json`, `formalization.yaml`, a root `LICENSE`, and
    a recorded NanoDa replay.

## Rank 4 in progress: pair-chain insertion (XP)

Source: `docs/research-ledger/RANK4_SAT_REDUCTION.md`, section "Pair-chain insertion (XP)".

**Statement XP(N)** (`N = 2m`). Let `S` be a basis of a rank-4 matroid `M`, and let
`A_0 … A_{m−1}` be an orientable pair chain of `M∖S`: every `A_i ∪ A_{i+1}` is a basis, as for the
consecutive pairs of a CBO. Then for some position `j` and some ordered split `S = P ⊔ Q`, the chain
`A_0 … A_j, P, Q, A_{j+1} … A_{m−1}` is valid and orientable. Old pairs may be re-oriented, and no
density is assumed. XP gives X′ in the form the proof uses. It is strictly stronger than contiguous
insertion, which fails for `N = 6, 8, 10, 12`, while XP holds there (exact SAT).

**Human reduction for `N ≥ 8`.** The reduction goes to four local lemmas on the 12 elements
`A_{j−1}, A_j, A_{j+1}, A_{j+2}, S`:

- orientability of a cycle of full-support 2×2 relations: a slack relation suffices, and an
  all-tight cycle is decided by parity;
- validity of the new split, by Greene–Magnanti basis-partition exchange;
- a choice of `j` that leaves every slack cycle a slack relation (`m ≥ 4`);
- local lemmas that close the tight cycles.

| Local lemma | LRAT hints |
|---|---|
| odd | 34,873 |
| even | 28,925 |
| P-cycle only | 8,650 |
| Q-cycle only | 7,713 |

The total is about 80k hints, against about 1.26M for the four X′ certificates it would replace.
These LRAT proofs were produced and checked outside Lean.

**Status.**

- The reduction is written in the ledger. Formalization is to happen on branch `probe/xp`, which at
  the time of writing has no commits beyond `probe/rank4` a4ead33.
- Hand proofs of the local lemmas are being sought. For the P-cycle lemma:
  - it fails for a valid split exactly when the split is *crossed*;
  - "not every valid split is crossed" is an 8-element claim (UNSAT, `crossed.py`);
  - if `(P, Q)` is crossed and valid, then `(Q, P)`, if valid, is uncrossed.

## Rank 4: earlier structural layers in the main library

The main library also contains the Sprint 1–5 structural work on the gcd-two case (human proofs,
formalized internal):

- pair-cycle orientation;
- local `2+2` repartition;
- the neighbor-closure obstructions `unique_adjacent_repartition_forces_neighbor_closure` and
  `exists_alternative_repartition_of_neighbor_closure_free`;
- repair dynamics, dangerous cores and density-slack deletion;
- the older divisible theorem `exists_cyclicBasisOrder_of_rank_four_of_nonempty_proper_tight`.

These results remain valid. Apart from the tight-set and dangerous-hyperplane reductions, the
rank-4 proof above does not use them.

The existence question they left open is settled mathematically. vHT with weight 2 on `ℤ/(2k+1)`
gives every uniformly dense rank-4 matroid on `4k+2` elements a chain of `2k+1` pairs, which is the
data of `AdmissiblePairCycle.Data M (2k+1) 2`. In Lean the fibre argument is so far done only for
`n = 10` (`Kum10Chain.lean`); no general constructor of `AdmissiblePairCycle.Data` exists.

Local repair is not enough on its own:

- rigid chains exist, for example Bérczi–Jánosik–Mátravölgyi's Example 12 (EJC Example 15), a
  sparse paving matroid on 10 elements;
- the local lemma "at most two re-splits inside a linear segment of `w` pairs break rigidity" is
  false (SAT) for `w = 6, …, 9`.

Exact finite evidence from those sprints, scoped to the certified objects:

- a strict 10-element binary fixed-pair obstruction, which another admissible pair cycle resolves;
- a strict 18-element binary obstruction whose 30,720-vertex adjacent-exchange component has
  maximum distance two to orientability;
- a four-block `GF(2)^4` local audit: the closure obstruction can occur on the left only, on the
  right only, or on both sides. So the disjunctive closure theorem must not be strengthened to
  require both sides.

## Rank 5 (research target)

- **Reduction.** Rank 5 is prime, so `solvesKUMAtRank_of_prime` reduces full KUM at rank 5 to the
  divisible sizes `n = 5k`. The coprime sizes are already formalized (main). `n = 5` is trivial.
- **KUM(5,10) is known** (computational evidence, not in Lean).
  - Garamvölgyi–Mizutani–Oki–Schwarcz–Yamaguchi (ICALP 2025, arXiv:2411.06771, Prop. 4.3) show by
    SAT that in rank at most 5 the only basis pair without an SI-ordering is the disjoint pair in
    `R10`.
  - `R10` satisfies Gabow's conjecture (Bérczi–Mátravölgyi–Schwarcz, for regular matroids). So
    Gabow's conjecture, and with it KUM(5,10), holds.
  - Our independent run `kum_r_n.py 5 10` is UNSAT (4,337 s). No certificate was produced.
  - Kotlar (2013) does not give rank 5, although it is sometimes cited for it.
- **The naive extension X′₅ does not transfer.**
  - The local block encoding of X′₅ (`ext_rank_r.py`) is SAT at `N = 10` and `N = 15`, including
    with density and with blocks covering 9 of the 10 elements.
  - The models have not been decoded into genuine matroids. So failure of X′₅ in general is
    strongly suggested but not proved.
  - For paving matroids X′ holds in every rank (McGuinness 2024, Prop. 13, contiguous insertion,
    no density). Our paving runs agree: X′₅(10) is UNSAT in 49 s and X′₅(15) in 206 s.
- **Open.** KUM(5,5k) for `k ≥ 3` needs a new extension idea for non-paving matroids.

## Literature

- **McGuinness**, *Cyclic orderings of paving matroids*, EJC 31(4) (2024) #P4.9, with a May 2025
  corrigendum for `|E| < 2r`. KUM for paving matroids; Prop. 13 is X′ for paving matroids in every
  rank.
- **Bérczi–Jánosik–Mátravölgyi**, EJC 33(1) (2026) #P1.20. For a split matroid with a partition
  into bases, there is a CBO in which every basis of the partition is an interval. In particular
  this gives KUM for such matroids.
- **Bonin**, Adv. Appl. Math. 50 (2013). KUM and Gabow's conjecture for sparse paving matroids.
- **Used in the formalization**:
  - van den Heuvel–Thomassé (Theorem 2.1, coprime KUM, covers);
  - Kotlar–Ziv (arXiv:1110.1826; Gabow in rank 4, hence KUM(4,8)).
- **Wiedemann** (1984 note): pair chains for `n = 4k`. Not formalized.

The full review is at
`C:\Users\auste\Downloads\HigherRankKUM\bsi_research_2026-09-24\KUM_LITERATURE_REVIEW.md`, outside
the repository.

## Other computational evidence (not in Lean)

- **Pair chains with re-splits** (`pairchain.py`):

  | `n` | chain | question | result | hints |
  |---|---|---|---|---|
  | 8 | Wiedemann | a CBO within one re-split | UNSAT | 6k |
  | 12 | Wiedemann | a CBO within one re-split | SAT | |
  | 12 | Wiedemann | a CBO within two re-splits | UNSAT | 2.4M |
  | 14 | vHT | a CBO within one re-split | SAT | |
  | 14 | vHT | a CBO within two re-splits | UNSAT | 749k |

  The general two-re-split question for `n ≥ 18` is open.
- **Insertion patterns.** Contiguous (one-block) insertion of `S` fails for every even `N` tested.
  Single-gap failures in general rank-4 matroids have 20 inclusion-minimal patterns; paving
  matroids have exactly one, up to symmetry.
- **An alternative KUM(4,10) route** (deletion plus a restricted X′(6), about 340k hints). It is
  superseded by `chain10`.

## Open research targets

1. **Human proofs of the remaining rank-4 certificates.**
   - The four XP local lemmas. Together with the XP formalization, they would remove all four X′
     certificates (1.26M hints).
   - `hit14g` and `hit14line`.
     - For `hit14g`, the ledger records a paper argument for the related Theorem G choice lemma
       (`RANK4_HEAVY_FLAT_SPLICE.md` §7).
     - `hit14line` has no written proof.
   - After these, only `chain10` (14.7k hints) would stand between rank 4 and a proof free of SAT.
2. **Migration and Palomar packaging.**
   - Move the probe proof into the main library, with the certificates in a separate library.
   - Write `Challenge.lean`, `Solution.lean`, `comparator.json` and `formalization.yaml`, and add a
     root `LICENSE`.
   - Run a NanoDa replay.
3. **Rank 5.** KUM(5,5k) for `k ≥ 3`, which needs an extension idea beyond X′₅. Bringing KUM(5,10)
   into Lean would need either a certificate or a human proof.
4. **General KUM.**
   - Divisible KUM at every rank.
   - At composite ranks, also the intermediate sizes with `1 < gcd(n, r) < r`, the analogue of
     rank 4's `n = 4k+2`.

See `docs/research-ledger/RANK4_FORMALIZATION_STATUS.md`, `RANK4_SAT_REDUCTION.md`,
`RANK4_EXTENSION_THEOREM.md`, `VHT_FORMALIZATION_PLAN.md`, `RANK5_EXTENSION_PROBE.md`,
`PALOMAR_PHASE0.md`, and, for the earlier sprints, `SPRINT1.md` to `SPRINT5_*.md`.
