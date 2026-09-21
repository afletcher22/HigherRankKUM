import Rank3KUM.HalfWeave.RankTwo
import Rank3KUM.UniformDensity
import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Fin

namespace Rank3KUM.HalfWeave

open Set

noncomputable section

variable {α : Type*}

/-- Ground elements are equivalent when their singleton closures agree. -/
def closureSetoid (M : Matroid α) : Setoid M.E where
  r e f :=
    M.closure ({(e : α)} : Set α) =
      M.closure ({(f : α)} : Set α)
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }

/-- The finite partition of the ground set into singleton-closure classes. -/
def closureFinpartition
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    Finpartition (Finset.univ : Finset M.E) := by
  classical
  exact Finpartition.ofSetoid (closureSetoid M)

@[simp] theorem mem_closureFinpartition_part_iff
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (e f : M.E) :
    f ∈ (closureFinpartition M).part e ↔
      M.closure ({(e : α)} : Set α) =
        M.closure ({(f : α)} : Set α) := by
  classical
  exact Finpartition.mem_part_ofSetoid_iff_rel



/-- Closure parts sorted by nonincreasing cardinality. -/
def sortedClosureParts
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    List (closureFinpartition M).parts :=
  ((closureFinpartition M).parts.attach.toList).insertionSort
    (fun p q => q.1.card ≤ p.1.card)

@[simp] theorem length_sortedClosureParts
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    (sortedClosureParts M).length =
      (closureFinpartition M).parts.card := by
  simp [sortedClosureParts]

@[simp] theorem mem_sortedClosureParts
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (p : (closureFinpartition M).parts) :
    p ∈ sortedClosureParts M := by
  simp [sortedClosureParts]

theorem nodup_sortedClosureParts
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    (sortedClosureParts M).Nodup := by
  apply
    (List.perm_insertionSort
      (fun p q :
        (closureFinpartition M).parts =>
          q.1.card ≤ p.1.card)
      ((closureFinpartition M).parts.attach.toList)).nodup_iff.mpr
  exact Finset.nodup_toList _

theorem pairwise_sortedClosureParts
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    (sortedClosureParts M).Pairwise
      (fun p q => q.1.card ≤ p.1.card) := by
  exact List.pairwise_insertionSort _ _

#print axioms Rank3KUM.HalfWeave.nodup_sortedClosureParts
#print axioms Rank3KUM.HalfWeave.pairwise_sortedClosureParts


/-- Enumerate closure parts in their nonincreasing-size order. -/
def sortedClosurePartsEquiv
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    Fin (closureFinpartition M).parts.card ≃
      (closureFinpartition M).parts := by
  let L := sortedClosureParts M
  have hlength :
      L.length = (closureFinpartition M).parts.card := by
    simp [L]
  have hnodup : L.Nodup := by
    simpa [L] using nodup_sortedClosureParts M
  have hall :
      ∀ p : (closureFinpartition M).parts,
        p ∈ L := by
    intro p
    simp [L]
  exact
    (finCongr hlength.symm).trans
      (hnodup.getEquivOfForallMemList _ hall)

#print axioms Rank3KUM.HalfWeave.sortedClosurePartsEquiv

/-- Sorted closure-part cardinalities are nonincreasing in their labels. -/
theorem antitone_sortedClosureParts_card
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    Antitone
      (fun i : Fin (closureFinpartition M).parts.card =>
        ((sortedClosurePartsEquiv M i).1).card) := by
  intro i j hij
  by_cases heq : i = j
  · subst j
    rfl
  have hlt : i.val < j.val := by
    omega
  let L := sortedClosureParts M
  have hlength :
      L.length = (closureFinpartition M).parts.card := by
    simp [L]
  let i' : Fin L.length :=
    Fin.cast hlength.symm i
  let j' : Fin L.length :=
    Fin.cast hlength.symm j
  have hpair :
      L.Pairwise
        (fun p q => q.1.card ≤ p.1.card) := by
    simpa [L] using pairwise_sortedClosureParts M
  have hrel :
      (L.get j').1.card ≤ (L.get i').1.card := by
    exact
      (List.pairwise_iff_getElem.mp hpair)
        i'.val j'.val i'.isLt j'.isLt
        (by simpa [i', j'] using hlt)
  have hi :
      sortedClosurePartsEquiv M i = L.get i' := by
    simp [sortedClosurePartsEquiv, L, i']
  have hj :
      sortedClosurePartsEquiv M j = L.get j' := by
    simp [sortedClosurePartsEquiv, L, j']
  change
    ((sortedClosurePartsEquiv M j).1).card ≤
      ((sortedClosurePartsEquiv M i).1).card
  rw [hi, hj]
  exact hrel

#print axioms Rank3KUM.HalfWeave.antitone_sortedClosureParts_card

/-- The sizes of the sorted closure parts sum to the ground-set cardinality. -/
theorem sum_sortedClosureParts_card
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    (∑ i : Fin (closureFinpartition M).parts.card,
      ((sortedClosurePartsEquiv M i).1).card) =
        Fintype.card M.E := by
  let P : Finpartition (Finset.univ : Finset M.E) :=
    closureFinpartition M
  calc
    (∑ i : Fin (closureFinpartition M).parts.card,
      ((sortedClosurePartsEquiv M i).1).card) =
        ∑ p : (closureFinpartition M).parts,
          p.1.card := by
      refine Fintype.sum_equiv
        (sortedClosurePartsEquiv M) _ _ ?_
      intro i
      rfl
    _ = ∑ p ∈ (closureFinpartition M).parts,
        p.card := by
      change
        (∑ p ∈ (closureFinpartition M).parts.attach,
          p.1.card) =
            ∑ p ∈ (closureFinpartition M).parts, p.card
      exact
        Finset.sum_attach
          (closureFinpartition M).parts
          (fun p : Finset M.E => p.card)
    _ = (Finset.univ : Finset M.E).card := by
      simpa [P] using P.sum_card_parts
    _ = Fintype.card M.E := by simp

#print axioms Rank3KUM.HalfWeave.sum_sortedClosureParts_card


/--
Flatten the sorted family of closure parts into contiguous
`(part index, offset)` coordinates.
-/
def sortedClosureSigmaEquiv
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k) :
    Fin (2 * k) ≃
      (i : Fin (closureFinpartition M).parts.card) ×
        Fin ((sortedClosurePartsEquiv M i).1).card := by
  have hsum :
      (∑ i : Fin (closureFinpartition M).parts.card,
        ((sortedClosurePartsEquiv M i).1).card) =
          2 * k := by
    rw [sum_sortedClosureParts_card M, hcard]
  exact
    (finCongr hsum.symm).trans
      finSigmaFinEquiv.symm

#print axioms Rank3KUM.HalfWeave.sortedClosureSigmaEquiv


/-- Prefix sum used by the standard flattening equivalence for finite sigma types. -/
def finSigmaPrefix
    {m : ℕ}
    (n : Fin m → ℕ)
    (r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range r,
    if h : i < m then n ⟨i, h⟩ else 0

theorem sum_fin_castLE_eq_finSigmaPrefix
    {m : ℕ}
    (n : Fin m → ℕ)
    (c : Fin m) :
    (∑ i : Fin c.val,
      n (Fin.castLE c.isLt.le i)) =
        finSigmaPrefix n c.val := by
  unfold finSigmaPrefix
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have him : i.val < m :=
    i.isLt.trans c.isLt
  rw [dif_pos him]
  apply congrArg n
  apply Fin.ext
  rfl

theorem finSigmaPrefix_succ
    {m : ℕ}
    (n : Fin m → ℕ)
    (r : ℕ)
    (hr : r < m) :
    finSigmaPrefix n (r + 1) =
      finSigmaPrefix n r + n ⟨r, hr⟩ := by
  simp [finSigmaPrefix, Finset.sum_range_succ, hr]

theorem finSigmaPrefix_add_le
    {m : ℕ}
    (n : Fin m → ℕ)
    {a b : Fin m}
    (hab : a < b) :
    finSigmaPrefix n a.val + n a ≤
      finSigmaPrefix n b.val := by
  rw [← finSigmaPrefix_succ n a.val a.isLt]
  unfold finSigmaPrefix
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (by omega)
  · intro i _ _
    exact Nat.zero_le _

/-- The block coordinate of the standard flattened finite sigma type is monotone. -/
theorem monotone_finSigmaFinEquiv_symm_fst
    {m : ℕ}
    {n : Fin m → ℕ} :
    Monotone
      (fun j : Fin (∑ i : Fin m, n i) =>
        (finSigmaFinEquiv.symm j).1) := by
  intro a b hab
  let E :
      ((i : Fin m) × Fin (n i)) ≃
        Fin (∑ i : Fin m, n i) :=
    finSigmaFinEquiv
  let x := E.symm a
  let y := E.symm b
  by_contra hxy
  have hyx : y.1 < x.1 :=
    lt_of_not_ge hxy
  have hxformula := finSigmaFinEquiv_apply x
  have hyformula := finSigmaFinEquiv_apply y
  have hxa : finSigmaFinEquiv x = a :=
    E.apply_symm_apply a
  have hyb : finSigmaFinEquiv y = b :=
    E.apply_symm_apply b
  rw [hxa] at hxformula
  rw [hyb] at hyformula
  rw [sum_fin_castLE_eq_finSigmaPrefix] at hxformula
  rw [sum_fin_castLE_eq_finSigmaPrefix] at hyformula
  have hpref :=
    finSigmaPrefix_add_le n hyx
  have hxoff : 0 ≤ x.2.val := Nat.zero_le _
  have hyoff : y.2.val < n y.1 := y.2.isLt
  change a.val ≤ b.val at hab
  change a.val =
    finSigmaPrefix n x.1.val + x.2.val at hxformula
  change b.val =
    finSigmaPrefix n y.1.val + y.2.val at hyformula
  omega

/-- Identify the ground subtype with the subtype of the universal finset. -/
def groundUnivFinsetEquiv
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    M.E ≃ (Finset.univ : Finset M.E) where
  toFun e := ⟨e, Finset.mem_univ e⟩
  invFun e := e.1
  left_inv _ := rfl
  right_inv _ := rfl

/-- Enumerate every closure part internally by its finite cardinality. -/
def closurePartsEnumeration
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    M.E ≃
      (p : (closureFinpartition M).parts) ×
        Fin p.1.card :=
  (groundUnivFinsetEquiv M).trans
    ((closureFinpartition M).equivSigmaParts.trans
      ((Equiv.refl _).sigmaCongr
        (fun p => p.1.equivFin)))

@[simp] theorem closurePartsEnumeration_part
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (e : M.E) :
    ((closurePartsEnumeration M e).1).1 =
      (closureFinpartition M).part e := by
  rfl

/-- Reindex the internally enumerated closure parts by decreasing size. -/
def sortedClosureCoordinatesEquiv
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E] :
    ((i : Fin (closureFinpartition M).parts.card) ×
      Fin ((sortedClosurePartsEquiv M i).1).card) ≃
        M.E :=
  (Equiv.sigmaCongrLeft
      (sortedClosurePartsEquiv M)).trans
    (closurePartsEnumeration M).symm

theorem part_sortedClosureCoordinatesEquiv
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (z :
      (i : Fin (closureFinpartition M).parts.card) ×
        Fin ((sortedClosurePartsEquiv M i).1).card) :
    (closureFinpartition M).part
        (sortedClosureCoordinatesEquiv M z) =
      (sortedClosurePartsEquiv M z.1).1 := by
  let q :
      (p : (closureFinpartition M).parts) ×
        Fin p.1.card :=
    ⟨sortedClosurePartsEquiv M z.1, z.2⟩
  change
    (closureFinpartition M).part
        ((closurePartsEnumeration M).symm q) =
      (sortedClosurePartsEquiv M z.1).1
  calc
    (closureFinpartition M).part
        ((closurePartsEnumeration M).symm q) =
      ((closurePartsEnumeration M
        ((closurePartsEnumeration M).symm q)).1).1 := by
          symm
          exact
            closurePartsEnumeration_part M
              ((closurePartsEnumeration M).symm q)
    _ = q.1.1 := by
      exact congrArg (fun x => x.1.1)
        ((closurePartsEnumeration M).apply_symm_apply q)
    _ = (sortedClosurePartsEquiv M z.1).1 := by
      rfl

/-- A ground-set enumeration in which closure classes form sorted contiguous blocks. -/
def sortedClosureGroundEquiv
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k) :
    Fin (2 * k) ≃ M.E :=
  (sortedClosureSigmaEquiv M k hcard).trans
    (sortedClosureCoordinatesEquiv M)

/-- The sorted closure-class label attached to a flattened ground position. -/
def sortedClosureBlock
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k) :
    Fin (2 * k) →
      Fin (closureFinpartition M).parts.card :=
  fun j => (sortedClosureSigmaEquiv M k hcard j).1

theorem monotone_sortedClosureBlock
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k) :
    Monotone (sortedClosureBlock M k hcard) := by
  have hsum :
      (∑ i : Fin (closureFinpartition M).parts.card,
        ((sortedClosurePartsEquiv M i).1).card) =
          2 * k := by
    rw [sum_sortedClosureParts_card M, hcard]
  intro a b hab
  change
    (finSigmaFinEquiv.symm
      (finCongr hsum.symm a)).1 ≤
    (finSigmaFinEquiv.symm
      (finCongr hsum.symm b)).1
  apply monotone_finSigmaFinEquiv_symm_fst
  change a.val ≤ b.val
  exact hab

theorem part_sortedClosureGroundEquiv
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k)
    (j : Fin (2 * k)) :
    (closureFinpartition M).part
        (sortedClosureGroundEquiv M k hcard j) =
      (sortedClosurePartsEquiv M
        (sortedClosureBlock M k hcard j)).1 := by
  simpa [sortedClosureGroundEquiv, sortedClosureBlock] using
    part_sortedClosureCoordinatesEquiv M
      (sortedClosureSigmaEquiv M k hcard j)

theorem mem_sortedClosurePart_iff_block_eq
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k)
    (j : Fin (2 * k))
    (c : Fin (closureFinpartition M).parts.card) :
    sortedClosureGroundEquiv M k hcard j ∈
        (sortedClosurePartsEquiv M c).1 ↔
      sortedClosureBlock M k hcard j = c := by
  let P : Finpartition (Finset.univ : Finset M.E) :=
    closureFinpartition M
  rw [← P.part_eq_iff_mem
    (sortedClosurePartsEquiv M c).2]
  rw [part_sortedClosureGroundEquiv]
  constructor
  · intro h
    apply (sortedClosurePartsEquiv M).injective
    exact Subtype.ext h
  · intro h
    subst c
    rfl

/-- Every block fiber is in bijection with its sorted closure part. -/
theorem card_fiberFinset_sortedClosureBlock
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k)
    (c : Fin (closureFinpartition M).parts.card) :
    (fiberFinset
      (sortedClosureBlock M k hcard) c).card =
        ((sortedClosurePartsEquiv M c).1).card := by
  exact
    Finset.card_bijective
      (sortedClosureGroundEquiv M k hcard)
      (sortedClosureGroundEquiv M k hcard).bijective
      (fun j => by
        simp only [fiberFinset, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact
          (mem_sortedClosurePart_iff_block_eq
            M k hcard j c).symm)

/-- Every sorted closure label occurs among the flattened ground positions. -/
theorem sortedClosureBlock_surjective
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k) :
    Function.Surjective
      (sortedClosureBlock M k hcard) := by
  intro c
  have hpart :
      ((sortedClosurePartsEquiv M c).1).Nonempty :=
    (closureFinpartition M).nonempty_of_mem_parts
      (sortedClosurePartsEquiv M c).2
  have hpos :
      0 < ((sortedClosurePartsEquiv M c).1).card :=
    Finset.card_pos.mpr hpart
  have hfiber :
      0 <
        (fiberFinset
          (sortedClosureBlock M k hcard) c).card := by
    rw [card_fiberFinset_sortedClosureBlock]
    exact hpos
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hfiber
  refine ⟨j, ?_⟩
  simpa [fiberFinset] using hj

theorem sortedClosureBlock_eq_iff_closure_eq
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k)
    (a b : Fin (2 * k)) :
    sortedClosureBlock M k hcard a =
        sortedClosureBlock M k hcard b ↔
      M.closure
          ({((sortedClosureGroundEquiv M k hcard a :
            M.E) : α)} : Set α) =
        M.closure
          ({((sortedClosureGroundEquiv M k hcard b :
            M.E) : α)} : Set α) := by
  let y := sortedClosureGroundEquiv M k hcard
  calc
    sortedClosureBlock M k hcard a =
        sortedClosureBlock M k hcard b ↔
      sortedClosureBlock M k hcard b =
        sortedClosureBlock M k hcard a := eq_comm
    _ ↔ y b ∈
        (sortedClosurePartsEquiv M
          (sortedClosureBlock M k hcard a)).1 :=
      (mem_sortedClosurePart_iff_block_eq
        M k hcard b
          (sortedClosureBlock M k hcard a)).symm
    _ ↔ M.closure
          ({((y a : M.E) : α)} : Set α) =
        M.closure
          ({((y b : M.E) : α)} : Set α) := by
      rw [← part_sortedClosureGroundEquiv
        M k hcard a]
      exact
        mem_closureFinpartition_part_iff
          M (y a) (y b)

#print axioms Rank3KUM.HalfWeave.groundUnivFinsetEquiv
#print axioms Rank3KUM.HalfWeave.closurePartsEnumeration
#print axioms Rank3KUM.HalfWeave.sortedClosureCoordinatesEquiv
#print axioms Rank3KUM.HalfWeave.sortedClosureGroundEquiv

/-- Every part of the closure partition inherits the uniform-density bound. -/
theorem card_closureFinpartition_part_le
    (M : Matroid α)
    (k : ℕ)
    (hDense : UniformlyDense M k)
    (hLoopless : M.Loopless)
    [Fintype M.E]
    [DecidableEq M.E]
    (p : Finset M.E)
    (hp : p ∈ (closureFinpartition M).parts) :
    p.card ≤ k := by
  let P : Finpartition (Finset.univ : Finset M.E) :=
    closureFinpartition M
  obtain ⟨e, he⟩ :=
    P.nonempty_of_mem_parts (by simpa [P] using hp)
  have hpart : P.part e = p :=
    P.part_eq_of_mem
      (by simpa [P] using hp) he
  have himage :
      (fun x : M.E => (x : α)) ''
          (↑p : Set M.E) ⊆
        M.closure ({(e : α)} : Set α) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxpart : x ∈ P.part e := by
      rw [hpart]
      exact hx
    have hclosure :
        M.closure ({(e : α)} : Set α) =
          M.closure ({(x : α)} : Set α) :=
      (mem_closureFinpartition_part_iff M e x).1
        (by simpa [P] using hxpart)
    rw [hclosure]
    exact M.mem_closure_self (x : α) x.property
  have hcardENat : (p.card : ℕ∞) ≤ (k : ℕ∞) := by
    calc
      (p.card : ℕ∞) =
          (↑p : Set M.E).encard := by simp
      _ =
          ((fun x : M.E => (x : α)) ''
            (↑p : Set M.E)).encard :=
        (Subtype.val_injective.encard_image
          (↑p : Set M.E)).symm
      _ ≤ (M.closure
          ({(e : α)} : Set α)).encard :=
        Set.encard_mono himage
      _ ≤ (k : ℕ∞) :=
        closure_singleton_encard_le
          M k hDense hLoopless e.property
  exact_mod_cast hcardENat

#print axioms Rank3KUM.HalfWeave.card_closureFinpartition_part_le

/-- Rank two forces the closure partition to have at least two parts. -/
theorem two_le_card_closureFinpartition_parts
    (M : Matroid α)
    [Fintype M.E]
    [DecidableEq M.E]
    (hRank : M.eRank = 2) :
    2 ≤ (closureFinpartition M).parts.card := by
  obtain ⟨e, f, he, hf, hclosure⟩ :=
    exists_pair_closure_ne_of_eRank_eq_two M hRank
  let e' : M.E := ⟨e, he⟩
  let f' : M.E := ⟨f, hf⟩
  let P : Finpartition (Finset.univ : Finset M.E) :=
    closureFinpartition M
  have hparts_ne : P.part e' ≠ P.part f' := by
    intro hparts
    have hfmem : f' ∈ P.part f' := by
      simp [P]
    have hfmem' : f' ∈ P.part e' := by
      rwa [hparts]
    apply hclosure
    exact
      (mem_closureFinpartition_part_iff M e' f').1
        (by simpa [P] using hfmem')
  have hsubset :
      ({P.part e', P.part f'} :
        Finset (Finset M.E)) ⊆ P.parts := by
    intro p hp
    simp only [Finset.mem_insert,
      Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [P]
  calc
    2 = ({P.part e', P.part f'} :
      Finset (Finset M.E)).card := by
        symm
        exact Finset.card_pair hparts_ne
    _ ≤ P.parts.card :=
      Finset.card_le_card hsubset

#print axioms Rank3KUM.HalfWeave.mem_closureFinpartition_part_iff
#print axioms Rank3KUM.HalfWeave.two_le_card_closureFinpartition_parts

/-- The canonical sorted closure blocks satisfy the half-weave hypotheses. -/
def sortedClosureBlockModel
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k)
    (hDense : UniformlyDense M k)
    (hLoopless : M.Loopless)
    (hRank : M.eRank = 2) :
    SortedBlockModel k
      (closureFinpartition M).parts.card where
  block := sortedClosureBlock M k hcard
  monotone_block :=
    monotone_sortedClosureBlock M k hcard
  surjective_block :=
    sortedClosureBlock_surjective M k hcard
  two_le_m :=
    two_le_card_closureFinpartition_parts M hRank
  fiber_card_le := by
    intro c
    rw [card_fiberFinset_sortedClosureBlock]
    exact
      card_closureFinpartition_part_le
        M k hDense hLoopless
        (sortedClosurePartsEquiv M c).1
        (sortedClosurePartsEquiv M c).2
  fiber_card_antitone := by
    intro c d hcd
    change
      (fiberFinset
        (sortedClosureBlock M k hcard) d).card ≤
      (fiberFinset
        (sortedClosureBlock M k hcard) c).card
    rw [card_fiberFinset_sortedClosureBlock,
      card_fiberFinset_sortedClosureBlock]
    exact antitone_sortedClosureParts_card M hcd

/-- Uniform density canonically supplies the sorted rank-two enumeration. -/
def rankTwoSortedEnumerationOfUniformlyDense
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hcard : Fintype.card M.E = 2 * k)
    (hDense : UniformlyDense M k)
    (hLoopless : M.Loopless)
    (hRank : M.eRank = 2) :
    RankTwoSortedEnumeration M k
      (closureFinpartition M).parts.card :=
  RankTwoSortedEnumeration.ofClosureBlocks
    M hLoopless
    (sortedClosureGroundEquiv M k hcard)
    (sortedClosureBlockModel
      M k hcard hDense hLoopless hRank)
    (sortedClosureBlock_eq_iff_closure_eq
      M k hcard)

#print axioms Rank3KUM.HalfWeave.sortedClosureBlockModel
#print axioms Rank3KUM.HalfWeave.rankTwoSortedEnumerationOfUniformlyDense

/-- Every finite uniformly dense rank-two matroid has the required cyclic adjacent-base order. -/
theorem exists_cyclic_adjacent_base_order_of_uniformlyDense
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hk : 0 < k)
    (hcard : Fintype.card M.E = 2 * k)
    (hDense : UniformlyDense M k)
    (hRank : M.eRank = 2) :
    ∃ order : Fin k × Bool ≃ M.E,
      ∀ p : Fin k × Bool,
        M.IsBase
          ({((order p : M.E) : α),
            ((order (weaveNext k hk p) : M.E) : α)} :
              Set α) := by
  have hLoopless : M.Loopless :=
    loopless_of_uniformlyDense M k hk hDense
  let D :=
    rankTwoSortedEnumerationOfUniformlyDense
      M k hcard hDense hLoopless hRank
  exact
    exists_cyclic_adjacent_base_order_of_sortedEnumeration
      M hk hRank D

#print axioms Rank3KUM.HalfWeave.exists_cyclic_adjacent_base_order_of_uniformlyDense

end

end Rank3KUM.HalfWeave
