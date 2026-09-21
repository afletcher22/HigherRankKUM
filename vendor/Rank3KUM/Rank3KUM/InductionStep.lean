import Rank3KUM.Splicing

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/-- Deleting a basis from a rank-three ground set of size `3k` leaves `3(k-1)` elements. -/
theorem delete_ground_encard_eq_three_mul_pred
    (M : Matroid α) (k : ℕ)
    (hk : 0 < k)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = ((3 * k : ℕ) : ℕ∞))
    {D : Set α}
    (hD : M.IsBase D) :
    (Matroid.delete M D).E.encard =
      ((3 * (k - 1) : ℕ) : ℕ∞) := by
  have hDcard : D.encard = (3 : ℕ∞) :=
    hD.encard_eq_eRank.trans hRank
  rw [Matroid.delete_ground]
  apply ENat.add_right_injective_of_ne_top
    (ENat.natCast_ne_top 3)
  calc
    (3 : ℕ∞) + (M.E \ D).encard =
        D.encard + (M.E \ D).encard := by
      rw [hDcard]
    _ = M.E.encard := by
      rw [← Set.encard_union_eq Set.disjoint_sdiff_right,
        Set.union_sdiff_cancel hD.subset_ground]
    _ = ((3 * k : ℕ) : ℕ∞) := hEcard
    _ = (3 : ℕ∞) +
        ((3 * (k - 1) : ℕ) : ℕ∞) := by
      have hnat :
          3 * k = 3 + 3 * (k - 1) := by
        omega
      calc
        ((3 * k : ℕ) : ℕ∞) =
            ((3 + 3 * (k - 1) : ℕ) : ℕ∞) :=
          congrArg (fun n : ℕ => (n : ℕ∞)) hnat
        _ = (3 : ℕ∞) +
            ((3 * (k - 1) : ℕ) : ℕ∞) :=
          ENat.natCast_add 3 (3 * (k - 1))

/--
The induction splice in the natural `3k` parametrization: once deleting a
three-element basis leaves a cyclic order on `3(k-1)` elements, the two-gap
theorem inserts that basis and returns a cyclic order on all `3k` elements.
-/
theorem exists_cyclicBasisOrder3_of_cyclic_basis_deletion
    (M : Matroid α) (k : ℕ)
    (hk : 3 ≤ k)
    (hRank : M.eRank = 3)
    {D : Set α}
    (hD : M.IsBase D)
    (hDelRank : (Matroid.delete M D).eRank = 3)
    (small : Fin (3 * (k - 1)) ≃
      (Matroid.delete M D).E)
    (hsmall :
      CyclicBasisOrder3 (Matroid.delete M D)
        (by omega) small) :
    ∃ order : Fin (3 * k) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  obtain ⟨order, horder⟩ :=
    contiguousBasisSplicing
      M hRank hD hDelRank
      (show 6 ≤ 3 * (k - 1) by omega)
      small hsmall
  let castIndex :
      Fin (3 * k) ≃ Fin (3 * (k - 1) + 3) :=
    finCongr (by omega)
  let fullOrder : Fin (3 * k) ≃ M.E :=
    castIndex.trans order
  refine ⟨fullOrder, ?_⟩
  intro i
  have hcyclic (j : ℕ) :
      castIndex (cyclicIndex (3 * k) (by omega) i j) =
        cyclicIndex (3 * (k - 1) + 3) (by omega)
          (castIndex i) j := by
    apply Fin.ext
    change
      (i.val + j) % (3 * k) =
        (i.val + j) % (3 * (k - 1) + 3)
    exact congrArg
      (fun n : ℕ => (i.val + j) % n)
      (show 3 * k = 3 * (k - 1) + 3 by omega)
  have hi := horder (castIndex i)
  change M.IsBase
    ({(order (castIndex i) : α),
      (order (castIndex
        (cyclicIndex (3 * k) (by omega) i 1)) : α),
      (order (castIndex
        (cyclicIndex (3 * k) (by omega) i 2)) : α)} :
        Set α)
  rw [hcyclic 1, hcyclic 2]
  exact hi

#print axioms Rank3KUM.delete_ground_encard_eq_three_mul_pred
#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_cyclic_basis_deletion

end

end Rank3KUM
