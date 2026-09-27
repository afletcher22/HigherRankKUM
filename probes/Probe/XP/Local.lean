import Probe.XP.Main

/-!
# Pair-chain insertion (XP): the local lemmas

Part A of `docs/research-ledger/XP_LOCAL_LEMMAS_ODD_EVEN.md`. Twelve elements: a basis `S` and four
consecutive pairs `A_{j-1} = X`, `A_j = A`, `A_{j+1} = B`, `A_{j+2} = Y` of the chain (as maps
`Bool → α`, first element at `false`). A split `(P, Q)` of `S` is inserted between `A` and `B`.
The new windows are

* `Wa = {last X'} ∪ A ∪ {first P'}`,  `Wb = {last A'} ∪ P ∪ {first Q'}`,
* `Wc = {last P'} ∪ Q ∪ {first B'}`,  `Wd = {last Q'} ∪ B ∪ {first Y'}`,

where primes are orientations. `local_xp` gives a valid split with:

* if `R_{j-1}` is tight (`{x, a, ā, b}` and `{x̄, a, ā, b̄}` are not bases), the P-side
  constraint `(e₁, e₂) ↦ ∃ o_P, Wa ∧ Wc` is `Good`;
* if `R_j` is tight (`{a, b, b̄, y}` and `{ā, b, b̄, ȳ}` are not bases), the Q-side constraint
  `(e₁, e₂) ↦ ∃ o_Q, Wb ∧ Wd` is `Good`.

Here `e₁` flips `X` and `e₂` flips `A`; the second argument of each side is the flip of `B`
(P side) and of `Y` (Q side) respectively, so both the EVEN and the ODD flip patterns can be read
off (`Good.diag`, `Good.common`).

Proof: the Main Lemma gives a valid split that is neither P-crossed nor Q-crossed. Each side is
then `Good` by `good_TT`: its two relations have full support (augmentation), and they do not
cross. Tightness identifies `X` with `B` in `M/A` and `Y` with `A` in `M/B` (`transfer_last`,
`transfer_first`).
-/

namespace HigherRankKUM.XP

open Set

variable {α : Type*} {M : Matroid α}

/-- Negating both arguments. -/
theorem Good.neg {T : Bool → Bool → Prop} (h : Good T) : Good (fun a b => T (!a) (!b)) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl ⟨h2, h1⟩
  · exact Or.inr ⟨h6.symm, h5.symm, h3.symm, h4.symm, h2.symm, h1.symm⟩

/-- **One side of Part A.** For a valid split that is not P-crossed, the P-side constraint is
`Good`. -/
theorem side_good (hRank : M.eRank = 4) (A B P Q : Bool → α)
    (hB : M.IsBase {A false, A true, B false, B true})
    (hS : M.IsBase {P false, P true, Q false, Q true})
    (hV : Valid M (A false) (A true) (B false) (B true) (P false) (P true) (Q false) (Q true))
    (hnc : ¬ PCrossed M (A false) (A true) (B false) (B true) (P false) (P true) (Q false)
      (Q true)) :
    Good (TT (fun i j => M.IsBase {B j, A false, A true, P i})
      (fun i j => M.IsBase {P i, Q false, Q true, B j})) := by
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 hRank hB
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 hRank hS
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 hRank hV.valA
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 hRank hV.valB
  have hBr : M.IsBase {B false, B true, A false, A true} := isBase_perm hB (by set_perm')
  have hE : ∀ x ∈ ({A false, A true, B false, B true} : Set α), x ∈ M.E := fun x hx =>
    hB.subset_ground hx
  have hES : ∀ x ∈ ({P false, P true, Q false, Q true} : Set α), x ∈ M.E := fun x hx =>
    hS.subset_ground hx
  apply good_TT
  · intro i
    cases i
    · exact exists_isBase_augment_first hRank (hV.valA.indep.subset (by sub_perm)) (by ne_tac)
        (by ne_tac) (by ne_tac) hBr
    · exact exists_isBase_augment_first hRank (hV.valA.indep.subset (by sub_perm)) (by ne_tac)
        (by ne_tac) (by ne_tac) hBr
  · intro j
    cases j
    · exact exists_isBase_augment hRank (hB.indep.subset (by sub_perm)) (by ne_tac) (by ne_tac)
        (by ne_tac) hV.valA
    · exact exists_isBase_augment hRank (hB.indep.subset (by sub_perm)) (by ne_tac) (by ne_tac)
        (by ne_tac) hV.valA
  · intro i
    cases i
    · exact exists_isBase_augment hRank (hS.indep.subset (by sub_perm)) (by ne_tac) (by ne_tac)
        (by ne_tac) hV.valB
    · exact exists_isBase_augment hRank (hS.indep.subset (by sub_perm)) (by ne_tac) (by ne_tac)
        (by ne_tac) hV.valB
  · intro j
    cases j
    · exact exists_isBase_augment_first hRank (hV.valB.indep.subset (by sub_perm)) (by ne_tac)
        (by ne_tac) (by ne_tac) hS
    · exact exists_isBase_augment_first hRank (hV.valB.indep.subset (by sub_perm)) (by ne_tac)
        (by ne_tac) (by ne_tac) hS
  · rintro ⟨i, h1, h2, h3, h4⟩
    apply hnc
    have hIB0 : M.Indep {B false, A false, A true} := hB.indep.subset (by sub_perm)
    have hIB1 : M.Indep {B true, A false, A true} := hB.indep.subset (by sub_perm)
    have hIP0 : M.Indep {P false, Q false, Q true} := hS.indep.subset (by sub_perm)
    have hIP1 : M.Indep {P true, Q false, Q true} := hS.indep.subset (by sub_perm)
    cases i
    · refine Or.inl ⟨?_, ?_, ?_, ?_⟩
      · exact mem_closure_of_not_isBase_last hRank hIB0 (by ne_tac) (by ne_tac) (by ne_tac)
          (hES _ (by simp)) h1
      · exact mem_closure_of_not_isBase_last hRank hIB1 (by ne_tac) (by ne_tac) (by ne_tac)
          (hES _ (by simp)) h2
      · exact mem_closure_of_not_isBase_last hRank hIP0 (by ne_tac) (by ne_tac) (by ne_tac)
          (hE _ (by simp)) h3
      · exact mem_closure_of_not_isBase_last hRank hIP1 (by ne_tac) (by ne_tac) (by ne_tac)
          (hE _ (by simp)) h4
    · refine Or.inr ⟨?_, ?_, ?_, ?_⟩
      · exact mem_closure_of_not_isBase_last hRank hIB0 (by ne_tac) (by ne_tac) (by ne_tac)
          (hES _ (by simp)) h1
      · exact mem_closure_of_not_isBase_last hRank hIB1 (by ne_tac) (by ne_tac) (by ne_tac)
          (hES _ (by simp)) h2
      · exact mem_closure_of_not_isBase_last hRank hIP1 (by ne_tac) (by ne_tac) (by ne_tac)
          (hE _ (by simp)) h3
      · exact mem_closure_of_not_isBase_last hRank hIP0 (by ne_tac) (by ne_tac) (by ne_tac)
          (hE _ (by simp)) h4

/-- Tightness of `R_{j-1}` identifies `x` with `b` in `M/A`: a window `{b, a₀, a₁, p}` that is a
basis gives the window `{x, a₀, a₁, p}`. -/
theorem transfer_last (hRank : M.eRank = 4) {x b a0 a1 p : α} (hxa : M.Indep {x, a0, a1})
    (h1 : x ≠ a0) (h2 : x ≠ a1) (h3 : a0 ≠ a1) (hba : M.Indep {b, a0, a1}) (h4 : b ≠ a0)
    (h5 : b ≠ a1) (ht : ¬ M.IsBase {x, a0, a1, b}) (hb : b ∈ M.E) (hp : p ∈ M.E)
    (h : M.IsBase {b, a0, a1, p}) : M.IsBase {x, a0, a1, p} := by
  have hb1 : b ∈ M.closure {x, a0, a1} :=
    mem_closure_of_not_isBase_last hRank hxa h1 h2 h3 hb ht
  have hb2 : b ∉ M.closure {a0, a1} := notMem_closure_of_indep_insert hba (by notin_tac)
  have hcl : M.closure {b, a0, a1} = M.closure {x, a0, a1} :=
    Matroid.closure_insert_congr ⟨hb1, hb2⟩
  have hp1 : p ∉ M.closure {b, a0, a1} := (isBase4_iff_last hRank hba h4 h5 h3 hp).1 h
  exact (isBase4_iff_last hRank hxa h1 h2 h3 hp).2 (by rw [← hcl]; exact hp1)

/-- Tightness of `R_j` identifies `y` with `a` in `M/B`: a window `{q, b₀, b₁, a}` that is a
basis gives the window `{q, b₀, b₁, y}`. -/
theorem transfer_first (hRank : M.eRank = 4) {y a b0 b1 q : α} (hby : M.Indep {y, b0, b1})
    (h1 : y ≠ b0) (h2 : y ≠ b1) (h3 : b0 ≠ b1) (hba : M.Indep {a, b0, b1}) (h4 : a ≠ b0)
    (h5 : a ≠ b1) (ht : ¬ M.IsBase {a, b0, b1, y}) (hy : y ∈ M.E) (hq : q ∈ M.E)
    (h : M.IsBase {q, b0, b1, a}) : M.IsBase {q, b0, b1, y} := by
  have hy1 : y ∈ M.closure {a, b0, b1} :=
    mem_closure_of_not_isBase_last hRank hba h4 h5 h3 hy ht
  have hy2 : y ∉ M.closure {b0, b1} := notMem_closure_of_indep_insert hby (by notin_tac)
  have hcl : M.closure {y, b0, b1} = M.closure {a, b0, b1} :=
    Matroid.closure_insert_congr ⟨hy1, hy2⟩
  have hIa : M.Indep {b0, b1, a} := hba.subset (by sub_perm)
  have hIy : M.Indep {b0, b1, y} := hby.subset (by sub_perm)
  have hq1 : q ∉ M.closure {b0, b1, a} := (isBase4_iff_first hRank hIa h3 h4.symm h5.symm hq).1 h
  refine (isBase4_iff_first hRank hIy h3 h1.symm h2.symm hq).2 ?_
  have e1 : ({b0, b1, y} : Set α) = {y, b0, b1} := by set_perm'
  have e2 : ({b0, b1, a} : Set α) = {a, b0, b1} := by set_perm'
  rw [e1, hcl, ← e2]
  exact hq1

/-- The pair `(x, y)` as a map `Bool → α`. -/
def pr (x y : α) : Bool → α
  | false => x
  | true => y

/-- **The local lemmas of XP.** -/
theorem local_xp (hRank : M.eRank = 4) {S : Set α} (hS : M.IsBase S) (X A B Y : Bool → α)
    (hAB : M.IsBase {A false, A true, B false, B true})
    (hXA : M.IsBase {X false, X true, A false, A true})
    (hBY : M.IsBase {B false, B true, Y false, Y true})
    (hdisj : Disjoint S {A false, A true, B false, B true}) :
    ∃ P Q : Bool → α, S = {P false, P true, Q false, Q true} ∧
      M.IsBase {A false, A true, P false, P true} ∧ M.IsBase {Q false, Q true, B false, B true} ∧
      ((¬ M.IsBase {X false, A false, A true, B false} ∧
          ¬ M.IsBase {X true, A false, A true, B true}) →
        Good (fun e1 e2 => ∃ oP, M.IsBase {X (!e1), A false, A true, P oP} ∧
          M.IsBase {P (!oP), Q false, Q true, B e2})) ∧
      ((¬ M.IsBase {A false, B false, B true, Y false} ∧
          ¬ M.IsBase {A true, B false, B true, Y true}) →
        Good (fun e1 e2 => ∃ oQ, M.IsBase {A (!e2), P false, P true, Q oQ} ∧
          M.IsBase {Q (!oQ), B false, B true, Y e1})) := by
  obtain ⟨p0, p1, q0, q1, hSeq, hV, hP, hQ⟩ := main_lemma hRank hAB hS hdisj
  have hS' : M.IsBase {p0, p1, q0, q1} := hSeq ▸ hS
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 hRank hAB
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 hRank hXA
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 hRank hBY
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 hRank hS'
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 hRank hV.valA
  obtain ⟨_, _, _, _, _, _⟩ := distinct4 hRank hV.valB
  have hEA : ∀ x ∈ ({A false, A true, B false, B true} : Set α), x ∈ M.E := fun x hx =>
    hAB.subset_ground hx
  have hEX : ∀ x ∈ ({X false, X true, A false, A true} : Set α), x ∈ M.E := fun x hx =>
    hXA.subset_ground hx
  have hEY : ∀ x ∈ ({B false, B true, Y false, Y true} : Set α), x ∈ M.E := fun x hx =>
    hBY.subset_ground hx
  have hES : ∀ x ∈ ({p0, p1, q0, q1} : Set α), x ∈ M.E := fun x hx => hS'.subset_ground hx
  refine ⟨pr p0 p1, pr q0 q1, hSeq, hV.valA, hV.valB, ?_, ?_⟩
  · -- the P side
    rintro ⟨t1, t2⟩
    have hg := side_good hRank A B (pr p0 p1) (pr q0 q1) hAB hS' hV hP
    refine Good.mono ?_ hg
    rintro e1 e2 ⟨o, h1, h2⟩
    refine ⟨o, ?_, h2⟩
    have hp : pr p0 p1 o ∈ M.E := by cases o <;> exact hES _ (by simp [pr])
    cases e1
    · simp only [Bool.not_false] at h1 ⊢
      exact transfer_last hRank (hXA.indep.subset (by sub_perm)) (by ne_tac) (by ne_tac)
        (by ne_tac) (hAB.indep.subset (by sub_perm)) (by ne_tac) (by ne_tac) t2
        (hEA _ (by simp)) hp h1
    · simp only [Bool.not_true] at h1 ⊢
      exact transfer_last hRank (hXA.indep.subset (by sub_perm)) (by ne_tac) (by ne_tac)
        (by ne_tac) (hAB.indep.subset (by sub_perm)) (by ne_tac) (by ne_tac) t1
        (hEA _ (by simp)) hp h1
  · -- the Q side, from the mirror
    rintro ⟨t1, t2⟩
    have hB' : M.IsBase {B false, B true, A false, A true} := isBase_perm hAB (by set_perm')
    have hS'' : M.IsBase {q0, q1, p0, p1} := isBase_perm hS' (by set_perm')
    have hV' : Valid M (B false) (B true) (A false) (A true) q0 q1 p0 p1 :=
      ⟨isBase_perm hV.valB (by set_perm'), isBase_perm hV.valA (by set_perm')⟩
    have hg := (side_good hRank B A (pr q0 q1) (pr p0 p1) hB' hS'' hV' hQ).neg
    refine Good.mono ?_ hg
    rintro e1 e2 ⟨o, h1, h2⟩
    refine ⟨!o, isBase_perm h2 (by set_perm'), ?_⟩
    rw [Bool.not_not]
    rw [Bool.not_not] at h1
    have hq : pr q0 q1 o ∈ M.E := by cases o <;> exact hES _ (by simp [pr])
    have h1' : M.IsBase {pr q0 q1 o, B false, B true, A e1} := isBase_perm h1 (by set_perm')
    cases e1
    · exact transfer_first hRank (hBY.indep.subset (by sub_perm)) (by ne_tac) (by ne_tac)
        (by ne_tac) (hAB.indep.subset (by sub_perm)) (by ne_tac) (by ne_tac) t1
        (hEY _ (by simp)) hq h1'
    · exact transfer_first hRank (hBY.indep.subset (by sub_perm)) (by ne_tac) (by ne_tac)
        (by ne_tac) (hAB.indep.subset (by sub_perm)) (by ne_tac) (by ne_tac) t2
        (hEY _ (by simp)) hq h1'

end HigherRankKUM.XP
