import HigherRankKUM.LowRank.RankTwo.LargestFirst
import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Max

namespace HigherRankKUM.RankTwo

noncomputable section

namespace FinitePartition

/-- Prefix sum for the standard flattening of a finite sigma type. -/
def sigmaPrefix {m : ℕ} (n : Fin m → ℕ) (r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range r, if h : i < m then n ⟨i, h⟩ else 0

private theorem sum_fin_castLE_eq_sigmaPrefix
    {m : ℕ} (n : Fin m → ℕ) (c : Fin m) :
    (∑ i : Fin c.val, n (Fin.castLE c.isLt.le i)) = sigmaPrefix n c.val := by
  unfold sigmaPrefix
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have him : i.val < m := i.isLt.trans c.isLt
  rw [dif_pos him]
  apply congrArg n
  apply Fin.ext
  rfl

private theorem sigmaPrefix_succ
    {m : ℕ} (n : Fin m → ℕ) (r : ℕ) (hr : r < m) :
    sigmaPrefix n (r + 1) = sigmaPrefix n r + n ⟨r, hr⟩ := by
  simp [sigmaPrefix, Finset.sum_range_succ, hr]

private theorem sigmaPrefix_add_le
    {m : ℕ} (n : Fin m → ℕ) {a b : Fin m} (hab : a < b) :
    sigmaPrefix n a.val + n a ≤ sigmaPrefix n b.val := by
  rw [← sigmaPrefix_succ n a.val a.isLt]
  unfold sigmaPrefix
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (by omega)
  · intro i _ _
    exact Nat.zero_le _

/-- The first coordinate of inverse standard sigma flattening is monotone. -/
theorem monotone_finSigmaFinEquiv_symm_fst
    {m : ℕ} {n : Fin m → ℕ} :
    Monotone (fun j : Fin (∑ i : Fin m, n i) => (finSigmaFinEquiv.symm j).1) := by
  intro a b hab
  let E : ((i : Fin m) × Fin (n i)) ≃ Fin (∑ i : Fin m, n i) := finSigmaFinEquiv
  let x := E.symm a
  let y := E.symm b
  by_contra hxy
  have hyx : y.1 < x.1 := lt_of_not_ge hxy
  have hxformula := finSigmaFinEquiv_apply x
  have hyformula := finSigmaFinEquiv_apply y
  have hxa : finSigmaFinEquiv x = a := E.apply_symm_apply a
  have hyb : finSigmaFinEquiv y = b := E.apply_symm_apply b
  rw [hxa] at hxformula
  rw [hyb] at hyformula
  rw [sum_fin_castLE_eq_sigmaPrefix] at hxformula
  rw [sum_fin_castLE_eq_sigmaPrefix] at hyformula
  have hpref := sigmaPrefix_add_le n hyx
  have hxoff : 0 ≤ x.2.val := Nat.zero_le _
  have hyoff : y.2.val < n y.1 := y.2.isLt
  change a.val ≤ b.val at hab
  change a.val = sigmaPrefix n x.1.val + x.2.val at hxformula
  change b.val = sigmaPrefix n y.1.val + y.2.val at hyformula
  omega

/--
Any finite partition of a `2k`-element finite type whose parts have size at
most `k` admits a contiguous enumeration with a largest part first.
-/
theorem exists_largestFirst_enumeration
    {β : Type*} [Fintype β] [DecidableEq β]
    (P : Finpartition (Finset.univ : Finset β))
    (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card β = 2 * k)
    (hbound : ∀ p : P.parts, p.1.card ≤ k) :
    ∃ y : Fin (2 * k) ≃ β,
      ∃ S : LargestFirstBlockModel k P.parts.card,
        ∀ a b : Fin (2 * k),
          S.block a = S.block b ↔ P.part (y a) = P.part (y b) := by
  classical
  have hβpos : 0 < Fintype.card β := by
    rw [hcard]
    omega
  have huniv_ne : (Finset.univ : Finset β) ≠ ∅ := by
    intro h
    have hzero : Fintype.card β = 0 := by
      simpa using congrArg Finset.card h
    omega
  have hparts : P.parts.Nonempty := P.parts_nonempty huniv_ne
  obtain ⟨p0, hp0⟩ := hparts
  let p0' : P.parts := ⟨p0, hp0⟩
  have hunivParts : (Finset.univ : Finset P.parts).Nonempty :=
    ⟨p0', Finset.mem_univ _⟩
  obtain ⟨pmax, _hpmax, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset P.parts)
      (fun p : P.parts => p.1.card) hunivParts
  let E : Fin P.parts.card ≃ P.parts := P.parts.equivFin.symm
  let imax : Fin P.parts.card := E.symm pmax
  have hpartsPos : 0 < P.parts.card := Finset.card_pos.mpr ⟨p0, hp0⟩
  let z : Fin P.parts.card := ⟨0, hpartsPos⟩
  let label : Fin P.parts.card ≃ P.parts := (Equiv.swap z imax).trans E
  have hlabel_zero : label z = pmax := by simp [label, imax, z]
  have hlabel_max : ∀ c : Fin P.parts.card,
      (label c).1.card ≤ (label z).1.card := by
    intro c
    rw [hlabel_zero]
    exact hmax (label c) (Finset.mem_univ _)
  have hsumParts : (∑ p : P.parts, p.1.card) = Fintype.card β := by
    calc
      (∑ p : P.parts, p.1.card) = ∑ p ∈ P.parts, p.card := by
        change (∑ p ∈ P.parts.attach, p.1.card) = ∑ p ∈ P.parts, p.card
        exact Finset.sum_attach P.parts (fun p : Finset β => p.card)
      _ = (Finset.univ : Finset β).card := P.sum_card_parts
      _ = Fintype.card β := by simp
  have hsumLabel :
      (∑ c : Fin P.parts.card, (label c).1.card) = 2 * k := by
    calc
      (∑ c : Fin P.parts.card, (label c).1.card) =
          ∑ p : P.parts, p.1.card := by
        refine Fintype.sum_equiv label _ _ ?_
        intro c
        rfl
      _ = Fintype.card β := hsumParts
      _ = 2 * k := hcard
  let flat : Fin (2 * k) ≃ (c : Fin P.parts.card) × Fin (label c).1.card :=
    (finCongr hsumLabel.symm).trans finSigmaFinEquiv.symm
  let univEquiv : β ≃ (Finset.univ : Finset β) :=
    (Equiv.subtypeUnivEquiv (fun x : β => Finset.mem_univ x)).symm
  let partEnum : β ≃ (p : P.parts) × Fin p.1.card :=
    univEquiv.trans
      (P.equivSigmaParts.trans
        ((Equiv.refl P.parts).sigmaCongr (fun p => p.1.equivFin)))
  let coords : ((c : Fin P.parts.card) × Fin (label c).1.card) ≃ β :=
    (Equiv.sigmaCongrLeft label).trans partEnum.symm
  let y : Fin (2 * k) ≃ β := flat.trans coords
  let block : Fin (2 * k) → Fin P.parts.card := fun j => (flat j).1
  have hpartEnum (x : β) : ((partEnum x).1).1 = P.part x := by rfl
  have hpart : ∀ j : Fin (2 * k), P.part (y j) = (label (block j)).1 := by
    intro j
    let q : (c : Fin P.parts.card) × Fin (label c).1.card := flat j
    let q' : (p : P.parts) × Fin p.1.card := (Equiv.sigmaCongrLeft label) q
    have happly : partEnum (partEnum.symm q') = q' := partEnum.apply_symm_apply q'
    have hfirst := congrArg (fun t => t.1.1) happly
    change P.part (partEnum.symm q') = q'.1.1
    rw [← hpartEnum]
    exact hfirst
  have hmono : Monotone block := by
    intro a b hab
    change
      (finSigmaFinEquiv.symm (finCongr hsumLabel.symm a)).1 ≤
        (finSigmaFinEquiv.symm (finCongr hsumLabel.symm b)).1
    apply monotone_finSigmaFinEquiv_symm_fst
    change a.val ≤ b.val
    exact hab
  have hmem : ∀ (j : Fin (2 * k)) (c : Fin P.parts.card),
      y j ∈ (label c).1 ↔ block j = c := by
    intro j c
    rw [← P.part_eq_iff_mem (label c).2]
    rw [hpart]
    constructor
    · intro h
      apply label.injective
      exact Subtype.ext h
    · intro h
      subst c
      rfl
  have hfiberCard : ∀ c : Fin P.parts.card,
      (fiberFinset block c).card = (label c).1.card := by
    intro c
    exact Finset.card_bijective y y.bijective
      (fun j => by
        simp only [fiberFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hmem j c).symm)
  have hfirstZero : ∀ hk' : 0 < k,
      block (firstIndex k (zeroFin k hk')) = z := by
    intro hk'
    let first : Fin (2 * k) := firstIndex k (zeroFin k hk')
    have hzpart : (label z).1.Nonempty := P.nonempty_of_mem_parts (label z).2
    have hzpos : 0 < (label z).1.card := Finset.card_pos.mpr hzpart
    let q : (c : Fin P.parts.card) × Fin (label c).1.card :=
      ⟨z, ⟨0, hzpos⟩⟩
    let j : Fin (2 * k) := flat.symm q
    have hj : block j = z := by
      change (flat j).1 = z
      simp [j, q]
    have hfirstj : first ≤ j := by
      change first.val ≤ j.val
      have hfirstval : first.val = 0 := by simp [first, firstIndex, zeroFin]
      omega
    have hle := hmono hfirstj
    rw [hj] at hle
    apply Fin.ext
    change (block first).val = 0
    change (block first).val ≤ z.val at hle
    have hle0 : (block first).val ≤ 0 := by simpa [z] using hle
    omega
  let S : LargestFirstBlockModel k P.parts.card :=
    { block := block
      monotone_block := hmono
      fiber_card_le := by
        intro c
        rw [hfiberCard]
        exact hbound (label c)
      first_fiber_largest := by
        intro hk' c
        rw [hfirstZero hk', hfiberCard, hfiberCard]
        exact hlabel_max c }
  refine ⟨y, S, ?_⟩
  intro a b
  change block a = block b ↔ P.part (y a) = P.part (y b)
  rw [hpart a, hpart b]
  constructor
  · intro h
    rw [h]
  · intro h
    apply label.injective
    exact Subtype.ext h

end FinitePartition

end

end HigherRankKUM.RankTwo
