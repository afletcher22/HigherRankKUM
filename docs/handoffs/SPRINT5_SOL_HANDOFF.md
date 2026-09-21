# Sol handoff — six-block locality and binary N=7 continuation

## Starting point and preservation

I inspected the live repository before continuing. It was much newer than the
old local Sprint 2 snapshot: `rank4-research-sprint4` was at
`23e572d9fa4df1ce1dbc0e2f114bab1819ba5ad3`.

I independently checked run `35151048294`: every listed step, including the
targeted Lean modules and full `lake build`, succeeded. The older pending-run
entry in `docs/research-ledger/SPRINT4.md` is stale; run `35143111762` was
cancelled, but the later current-head run is green.

My additions are isolated on `rank4-sprint5-six-block-audit`, based exactly on
that green commit. I did not modify your Sprint 4 branch, merge a PR, alter
Lean source/imports, touch dependency pins or frozen vendor content, or launch
duplicate CI. This continuation adds computational certificates and a research
note, not a new formal Lean result.

## New results

1. Exhaustive normalized binary N=7 audit: **25,152** unorientable admissible
   pair cycles; all strictly dense; all have an orientable **cross** repair.
   **728** have no strict-Phi-increasing repair, confirming that the escape
   alternative is necessary. N=5 reproduces the historical 80 obstructions.
2. Every positive repair was converted to an explicit permutation of labelled
   ground elements and every cyclic four-window independently rank-checked by
   span enumeration. No parallel labels were collapsed.
3. A representation-free informal six-block criterion determines repair
   admissibility, changed orientation parity/slack, and exact Delta Phi.
   All **209,736** finite move occurrences pass local-vs-global comparison.
4. A separate exhaustive binary six-block classification covers **65,536**
   contexts and **74,752** nonidentity moves. Among the **5,120** moves that
   preserve all four forced relations, **none changes their combined parity**.
   Therefore binary adjacent escape must create slack; a forced-to-forced
   parity escape is not available. This local computational result applies to
   odd cycle lengths N>=5, not just N=7, via the normalization argument.

The full statements, normalization/exhaustiveness argument, formulas, counts,
and evidence boundaries are in
`docs/research-ledger/SPRINT5_SIX_BLOCK_AUDIT.md`.

## Files and validation

Run:

```bash
python3 experiments/sprint5_verify.py
```

Added certificates:

- `experiments/sprint5_n7_escape_ascent_audit.py`
- `experiments/sprint5_n7_escape_ascent_result.json`
- `experiments/sprint5_six_block_parity_audit.py`
- `experiments/sprint5_six_block_parity_result.json`
- `experiments/sprint5_verify.py`

The verifier runs both bounded exact audits and checks the committed JSON
outputs, with a 120-second timeout per script. All tests passed locally.
The inherited Lean checkpoint is green and unchanged; no new Lean validation
is claimed or needed for these Python/docs-only additions.

## Recommended next task

Try to prove the **local rigidity-preserving parity conservation lemma**
mathematically, initially for binary representations. Normalize the middle
basis C union D, use the four rank-two endpoint projections, and show that
when an admissible replacement leaves all four relations forced, their XOR
cannot change. The exact finite classification supplies a regression oracle.

Only then test extension beyond binary matroids. In the general matroid
argument, keep both slack escape and forced-parity escape available unless
you prove the latter impossible. Binary evidence alone does not do that.

For the global existence argument, use the six-block formulas to study
boundaries at which **every** legal repair fails both slack and strict ascent.
An obstruction-to-tightness proof or a controlled propagation argument would
be valuable. Do not replace “some repair increases Phi” with “every repair
that remains forced increases Phi”: the local audit explicitly has negative,
zero, and positive changes, and legal repairs are reversible.

The formal relation-to-flattened-CBO bridge is still open; I did not close it
by silently redefining orientability. The executable positive-order checks are
evidence for this finite experiment, not a substitute for that Lean theorem.

## What not to claim

- 25,152 nonisomorphic matroids (these are normalized pair cycles).
- Universal one-step repair (the 18-element counterexample remains).
- Representation-free parity conservation (only binary locally certified).
- A proof of the global escape-or-ascent hypothesis.
- A full rank-four or full KUM solution.
- Literature novelty; it has not been audited for the new finite result.

Review/cherry-pick this isolated continuation before combining it with further
changes on your active research branch. No existing research work was reset.
