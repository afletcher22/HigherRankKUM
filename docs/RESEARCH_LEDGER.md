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

## Claims under audit

| ID | Claim | Evidence status | Scope | Current state |
| --- | --- | --- | --- | --- |
| S0-A | Coprime KUM covers rank four with odd ground-set size | published proof | generic | verify theorem statement and arithmetic scope |
| S0-B | Integral uniform density gives a partition into bases, hence some density-preserving basis deletion | checked informal derivation / literature-supported | generic | verify against matroid partition and McGuinness Prop. 2.3 |
| S0-C | Proper tight sets can be glued at arbitrary rational density, not only integer density | conjectural derivation pending audit | generic | check arithmetic, contraction density, scheduling, wraparound |
| S0-D | Rank-four `|E|=8` is covered by rank-four serial symmetric exchange | published proof pending exact implication audit | rank-specific | verify Kotlar–Ziv theorem and cyclic-order equivalence |
| S0-E | All paving matroids satisfy KUM | published proof | class-specific | verify McGuinness theorem and exact hypotheses |
| S0-F | Split matroids partitioned into bases have a stronger cyclic ordering | published proof | class-specific | verify Bérczi–Jánosik–Mátravölgyi theorem |
| S0-G | Current HigherRankKUM internally supplies divisible ranks 1, 2, 3 and divisible rank-4 proper-tight reduction | Lean verified at prior checkpoint | rank-specific | inspect immutable current declarations and exact theorem types |

## Active proof routes

1. **Insertion/control route for integral rank four.** Deletion existence is not the research question; the issue is choosing/using a deleted basis so reinsertion can be controlled.
2. **gcd-two scheduling/orientation route.** Audit rational tight gluing first; for strict `4k+2`, investigate the pair-cycle/2-SAT formulation only after Sprint 0.

## Deferred routes

- graph-three-trees route;
- real-representation/base-polytope route;
- unrestricted full-proof search.

## Sprint log

### Entry 0.1 — plan ingestion

Sol's staged plan was read in full. Two agenda-changing points are provisionally accepted for checking rather than assumed: integral-density deletion existence is already a matroid-partition consequence, and the proposed rational tight-set gluing may remove the proper-tight branch at nonintegral densities as well.

### Entry 0.2 — supplied literature review

The supplied literature chronology is useful as background, but Sprint 0 will use a narrower theorem-level ledger. Particular attention will be paid to van den Heuvel–Thomassé, McGuinness, Kotlar–Ziv, and Bérczi–Jánosik–Mátravölgyi, plus recent citing work that could strengthen the rank-four coverage.

## End-of-sprint fields

**Proved:** pending.

**Refuted:** pending.

**Unsupported:** pending.

**Single next task:** pending.
