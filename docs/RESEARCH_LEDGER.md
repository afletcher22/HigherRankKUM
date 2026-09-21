# HigherRankKUM Research Ledger

This ledger is the running record for higher-rank KUM research. It is deliberately separate from proof-source files so exploratory claims can be tracked without silently entering the trusted formal layer.

## Status vocabulary

**Evidence status:** `published proof`, `checked informal derivation`, `Lean verified`, `computational evidence`, `conjectural`, `refuted`.

**Scope:** `generic`, `rank-specific`, `class-specific`.

Every research claim should record both status and scope. A failed strengthening or failed insertion scheme is not a counterexample to KUM unless the KUM statement itself is what was tested.

## Working rules

- Record exact hypotheses and conclusions before testing a claim.
- Preserve counterexamples/witnesses and the smallest supporting script or certificate.
- For representable experiments record field, matrix, seed, and filters.
- Recheck rank, uniform density, strictness, and other hypotheses after deletion/contraction/minimization.
- Keep at most two serious proof routes active.
- Reserve full GitHub Actions CI for meaningful checkpoints; ordinary research commits stay on non-PR branches.
- End each sprint with: proved, refuted, unsupported, and the single next task.

---

# Sprint 0 — establish the actual starting point

**Start date:** 2026-09-14 (America/Phoenix)

**Branch:** `rank4-research-sprint0`

**Base commit:** `a13f2e912eecb1cd1c86bffe7f8a3751f96a5e74`

**Question:** What can HigherRankKUM use today without silently assuming an unproved or stronger theorem?

**Expected certificate:** source-backed literature ledger + immutable repository audit + corrected rank-four coverage table + one recommended next sprint.

**Budget:** targeted source inspection and paper derivations only. No broad computational campaign. No full CI unless Sprint 0 produces a code change worth promotion.

## Repository baseline

- HigherRankKUM audited source: `a13f2e912eecb1cd1c86bffe7f8a3751f96a5e74`.
- Lean toolchain: `leanprover/lean4:v4.33.0-rc2`.
- mathlib input revision: `v4.33.0-rc2`; resolved mathlib commit: `51e6992efd06126df61a496bebf8f49482a4e129`.
- Vendored Rank3KUM source: `eff642a2e01fac4fc1f6f76e592eeea46c3152c9`; exact vendored `Rank3KUM/` tree SHA `a73e2f94c811a4f2f072e197d1a03656bc53f616`.
- Prior independently observed build evidence: vendoring validation run `34934896378` and normal PR CI run `34935519633` both succeeded before Sprint 0. No new full build was launched for this research sprint.
- The CI-only cleanup commit `a13f2e9...` changed workflow triggers, not Lean proof source.

### Formal semantic boundary

`HigherRankKUM.CyclicBasisOrder M r hn σ` checks `M.IsBase` for the `r`-element cyclic window at **every** starting position. The abstract predicate permits an arbitrary codomain set `E`, but production solver theorems instantiate `σ : Fin n ≃ M.E`, so the formal solver interface is a bijective cyclic enumeration of the actual ground set.

Uniform density in the current generic core is the **integer-density** predicate

`|X| ≤ k r(X)`

for a natural parameter `k`. `Tight` is equality in this integer bound. Consequently the existing `TightFactorReduction` and `TightInduction` do not already state rational-density gluing.

### Declaration-level status

The existing `docs/MIGRATION_MANIFEST.md` remains the declaration-level copy/depend/rewrite/leave-behind manifest. Material facts checked at the immutable baseline:

- rank 1: native HigherRankKUM proof;
- rank 2: native compressed HalfWeave proof;
- rank 3: frozen vendored v3 proof plus the narrow `LowRank/RankThree.lean` adapter;
- `solvesDivisibleKUMAtRank_three` is explicit and uses no external live Rank3KUM dependency;
- generic tight induction is divisible/integer-density only;
- `Rank4/TightReduction.lean` is unconditional for rank four on `4k` elements with a nonempty proper tight set.

## Theorem-level literature ledger

| ID | Source / theorem | Exact usable conclusion | Evidence | Scope | Project implication |
| --- | --- | --- | --- | --- | --- |
| L1 | van den Heuvel–Thomassé, Theorem 3.1 | For loopless rank `r`, size `m`, `gcd(r,m)=1`, uniform density iff a cyclic basis ordering exists. | published proof | generic | Rank 4 with odd `m` is settled. |
| L2 | van den Heuvel–Thomassé, Corollary 3.2 | The general `w`-window coprime statement follows by truncating to rank `w`. | published proof | generic | Confirms the standard KUM formulation subsumes the universal `w`-window problem via truncation. |
| L3 | McGuinness, Theorem 1.3 | Every uniformly dense paving matroid is cyclically orderable. | published proof | class-specific | All paving rank-4 cases are removed at every density ratio. |
| L4 | McGuinness, Theorem 2.2 + Proposition 2.3 proof, integral subcase | A suitable matroid-partition theorem yields `k` bases in the integral case; deleting one gives density parameter `k-1`. The difficult nonintegral deletion argument uses paving. | published proof + checked deduction | generic integral deletion / paving beyond it | Do not research mere existence of some density-preserving basis deletion in the integral case. Research extra control and reinsertion. |
| L5 | Kotlar–Ziv, Conj. 1.1/1.2 equivalence + Theorem 4.2 | Two disjoint bases of a rank-4 matroid admit a full serial symmetric exchange, equivalently a cyclic ordering of their union with every four consecutive elements a basis. | published proof | rank-specific | Any uniformly dense rank-4 matroid on 8 elements is covered once matroid partition supplies two bases. |
| L6 | Bérczi–Jánosik–Mátravölgyi, Conjecture 3 + Theorem 1 | If a split matroid's ground set is partitioned into pairwise disjoint bases, there is a CBO in which the prescribed bases are consecutive intervals. | published proof | class-specific, integral | Covers integral-density split matroids. Does **not** by itself cover nonintegral uniformly dense split matroids. |
| L7 | Bérczi–Jánosik–Mátravölgyi, introductory use of matroid union | `k r(X) ≥ |X|` for all `X` characterizes coverage by `k` bases. | published citation to Edmonds–Fulkerson | generic | Gives a primary-source route to the integral partition argument; exact Lean library theorem still not located. |

### Literature caution

Rank-at-most-four/five statements appearing around the split-matroid literature can concern **Gabow / prescribed two-base exchange**, not KUM in full. Do not transfer those rank bounds to KUM without checking the statement.

A targeted search of recent citing work found no stronger general KUM theorem that removes the strict rank-four frontier. This is a targeted check, not an exhaustive novelty determination.

## Claims audit

| ID | Claim | Evidence status | Scope | Sprint 0 verdict |
| --- | --- | --- | --- | --- |
| S0-A | Coprime KUM covers rank four with odd ground-set size | published proof | generic | **verified** (vHT Thm. 3.1) |
| S0-B | Integral uniform density gives a partition into bases, hence some density-preserving basis deletion | published theorem + checked derivation | generic | **verified mathematically**; no convenient pinned-mathlib declaration located yet |
| S0-C | Proper tight sets can be glued at arbitrary rational density, not only integer density | checked informal derivation | generic | **derivation checks out on paper; not Lean verified; novelty not established** |
| S0-D | Rank-four `|E|=8` is covered by rank-four serial symmetric exchange | published proof + elementary deduction | rank-specific | **verified** (Kotlar–Ziv Thm. 4.2 + equivalent CBO formulation) |
| S0-E | All paving matroids satisfy KUM | published proof | class-specific | **verified** (McGuinness Thm. 1.3) |
| S0-F | Split matroids partitioned into bases have a stronger cyclic ordering | published proof | class-specific | **verified with integral/partition qualification** |
| S0-G | HigherRankKUM internally supplies divisible ranks 1,2,3 and divisible rank-4 proper-tight reduction | Lean verified at prior checkpoint + source audit | rank-specific | **verified at audited source commit** |

## Rational tight-set gluing audit

Let `n/r = p/q` in lowest terms, so `n = pg`, `r = qg`, `g = gcd(n,r)`. If nonempty proper `X` is tight and has rank `s`, then

`q | s`, say `s = qa` with `0 < a < g`, and `|X| = pa`.

The contraction has rank `q(g-a)` and complement size `p(g-a)`. Restriction density is immediate. Contraction density follows by applying the original density inequality to `A ∪ X`, subtracting tightness of `X`, and using the contraction rank formula.

For gluing, repeat a length-`g` binary pattern with `a` restriction slots and `g-a` contraction slots exactly `p` times. A global rank window has length `qg`, hence spans exactly `q` whole periods regardless of its starting residue. It therefore contains exactly `qa=s` restriction slots and `q(g-a)` contraction slots. In each factor these are consecutive entries of its own cyclic order. Their factor bases unite to a basis of `M` by the restriction/contraction basis-lifting theorem.

**Status:** checked informal derivation. Arithmetic and wraparound are sound. The existing Lean scheduler is the special case `q=1`; a new rational/full-density interface is genuinely needed for formalization.

For rank four with `|E|=4k+2`, `g=q=2`; a proper tight set must have rank 2 and size `2k+1`. Both factors are rank 2 on `2k+1` elements, hence coprime and covered by van den Heuvel–Thomassé. Alternation is exactly the `g=2,a=1` schedule. Thus the **proper-tight gcd-two branch is mathematically settled**, but not yet end-to-end Lean verified inside HigherRankKUM.

## Recovered rank-four experimental evidence

Artifact: File Library `rank4_binary_pair_cycle_exact.py` (6 Aug 2026).

The script studies binary rank-four admissible pair cycles `P_0,...,P_{m-1}` where every adjacent pair-union is a basis. A fixed pair cycle can be oriented by Boolean choices; rigid local relations produce a parity obstruction.

Recorded exact enumeration (up to the script's GL(4,2) normalization):

- `m=5` pairs (10 elements): 80 rigid parity obstructions to pure pair orientation; **all** admit a one-break local repair.
- `m=7` pairs (14 elements): 25,152 rigid parity obstructions; **all** admit a one-break repair.
- `m=9` pairs (18 elements): 6,723,840 rigid parity obstructions; 480 resist every one-break repair; all 480 admit the tested distance-two double-break repair affecting four consecutive pair blocks.

**What this refutes:**

> Every admissible fixed pair cycle in binary rank four can be made into a CBO merely by orienting its pairs.

It also refutes, at the tested 18-element binary level, the stronger claim that one local merged-pair break always repairs every rigid parity obstruction.

**What it does NOT refute:** KUM; existence of another admissible pair cycle/circular representation; existence of a CBO; or a bounded repair theorem with two or more local repairs.

The artifact should be independently rerun/certified before publication-quality reliance. Sprint 0 treats its current status as **computational evidence / recovered exact-search claim**, not a formal theorem.

## Corrected rank-four coverage map

For a finite uniformly dense rank-four matroid `M`, with `m=|E(M)|`:

| Case | Mathematical status after Sprint 0 | Formal HigherRankKUM status |
| --- | --- | --- |
| `m` odd | settled by vHT coprime theorem | external literature theorem, not Lean formalized here |
| `m=4k`, nonempty proper tight set | settled | **Lean verified** using internal ranks 1–3 |
| `m=4k+2`, nonempty proper tight set | settled by rational rank-2 gluing deduction + vHT | not yet formalized in current integer-density interface |
| `m=4` | trivial | can be derived if needed |
| `m=6` | settled mathematically (duality/rank-2 or paving route) | duality bridge not yet audited/formalized here |
| `m=8` | settled by partition into two bases + Kotlar–Ziv rank-4 theorem | literature-dependent, not end-to-end Lean |
| paving | settled by McGuinness | external literature theorem |
| integral-density split | settled by BJM | external literature theorem |
| strict `m=4k` outside covered classes | unresolved | research frontier |
| strict `m=4k+2` outside covered classes | unresolved | research frontier |

The smallest parameter not eliminated by this table is `(r,m)=(4,10)`. The first potentially open integral-density size is `m=12`.

## Active proof routes after recovered evidence

1. **Insertion/control route for integral rank four.** Matroid partition already supplies a deletable basis preserving integral density. The research question is what extra constraints on the basis/order enable reinsertion.
2. **gcd-two scheduling/repair route.** Pure orientation of an arbitrary fixed admissible pair cycle is already refuted. The live questions are whether one can choose a favorable representation/pair cycle, or prove a bounded structural repair theorem.

## Deferred routes

- graph-three-trees route;
- real-representation/base-polytope route;
- unrestricted full-proof search.

## Mathlib implementation note

A preliminary code search did not locate an obvious existing theorem in mathlib implementing Edmonds/Fulkerson matroid union/partition at the required generality. This is **not** a claim that mathlib lacks it. Before formalizing integral deletion existence, search the pinned revision more carefully. In any event, Sprint 1 does not need to formalize matroid partition merely to prove rational tight gluing.

## Sprint log

### Entry 0.1 — plan ingestion

Sol's staged plan was read in full. Two agenda-changing points were treated as claims to check: integral-density deletion existence is already a matroid-partition consequence, and rational tight-set gluing may remove the proper-tight branch at nonintegral densities as well.

### Entry 0.2 — supplied literature review

The supplied chronology is retained as background. The operational ledger uses theorem-level records. Kotlar–Ziv is added because it is essential for the rank-four eight-element base case.

### Entry 0.3 — immutable repository audit

The current generic code was inspected at `a13f2e9...`. Its cyclic-order semantics match the intended basis-window notion at production theorem interfaces. The current tight-set induction is genuinely integer/divisible and therefore does not already contain the rational-density theorem proposed for Sprint 1.

### Entry 0.4 — primary-source checks

The exact coprime/truncation, paving, rank-four two-base exchange, and split-matroid statements were checked against primary papers. The integral deletion observation is explicitly visible in McGuinness's Proposition 2.3 proof when the remainder `ℓ=0`.

### Entry 0.5 — rational gluing paper check

The proposed rational tight-set argument was independently followed through arithmetic, density inheritance, scheduling, cyclic wraparound, and basis gluing. No mathematical gap was found. Status remains checked informal derivation until formalized/reviewed.

### Entry 0.6 — recovered failed strengthening

The binary pair-cycle exact-search artifact records fixed-cycle orientation obstructions already at 10 elements. This prevents Sprint 3 from wasting time on an already-refuted universal orientation claim.

## End-of-sprint fields

**Proved / verified:** The published theorem scopes L1–L7 above; current divisible formal boundary; paper correctness of the rational tight-set derivation; rank-four proper-tight `4k+2` deduction on paper.

**Refuted:** Universal orientability of every fixed admissible binary rank-four pair cycle; one-break repair sufficiency for every tested rigid binary pair cycle at 18 elements.

**Unsupported / not yet certified:** Novelty of rational tight gluing; a Lean formalization of rational density/full-rank KUM; a pinned-mathlib matroid-partition theorem; publication-grade independent rerun of the recovered pair-cycle enumeration; any claim that strict rank-four KUM is solved.

**Single next task:** Sprint 1 — introduce a rational/full-density KUM interface and prove the rational tight-set gluing/reduction with exact quantifiers, while keeping external literature results as explicit assumptions rather than axioms.
