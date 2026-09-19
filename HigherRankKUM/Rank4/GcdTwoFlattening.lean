import HigherRankKUM.BalancedInterleave
import HigherRankKUM.Rank4.GcdTwoRepairGeometry

namespace HigherRankKUM
namespace Rank4GcdTwoFlattening

open Set
open PairCycle

noncomputable section

variable {α : Type*}

/-- In a labelled pair, slot `false` is the first element chosen by the
orientation bit and slot `true` is the other element. -/
def orientBit (x slot : Bool) : Bool :=
  if slot then Bool.not x else x

@[simp] theorem orientBit_false (x : Bool) : orientBit x false = x := by
  simp [orientBit]

@[simp] theorem orientBit_true (x : Bool) : orientBit x true = Bool.not x := by
  simp [orientBit]

@[simp] theorem orientBit_involutive (x b : Bool) :
    orientBit x (orientBit x b) = b := by
  cases x <;> cases b <;> rfl

/-- A transparent equivalence between the two positions of a pair and Bool.
Unlike mathlib's general `finTwoEquiv`, this reduces directly on the two
numeral positions used throughout the flattening proof. -/
def finTwoBoolEquiv : Fin 2 ≃ Bool where
  toFun
    | ⟨0, _⟩ => false
    | ⟨1, _⟩ => true
  invFun
    | false => 0
    | true => 1
  left_inv i := by fin_cases i <;> rfl
  right_inv b := by cases b <;> rfl

@[simp] theorem finTwoBoolEquiv_zero :
    finTwoBoolEquiv (0 : Fin 2) = false := rfl

@[simp] theorem finTwoBoolEquiv_one :
    finTwoBoolEquiv (1 : Fin 2) = true := rfl

/-- Relabel every pair by its chosen orientation. -/
def orientationEquiv {N : ℕ} (o : Fin N → Bool) :
    Fin N × Bool ≃ Fin N × Bool where
  toFun z := (z.1, orientBit (o z.1) z.2)
  invFun z := (z.1, orientBit (o z.1) z.2)
  left_inv z := by
    rcases z with ⟨i, b⟩
    simp
  right_inv z := by
    rcases z with ⟨i, b⟩
    simp

/-- Flatten an oriented cycle of pairs into an element order. -/
def orientedPairOrder
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN)
    (o : Fin N → Bool) :
    Fin (2 * N) ≃ M.E :=
  (blockPositionEquiv 2 N).symm |>.trans
    ((Equiv.prodCongr (Equiv.refl (Fin N)) finTwoBoolEquiv).trans
      ((orientationEquiv o).trans A.pairEquiv))

@[simp] theorem orientedPairOrder_block_zero
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN)
    (o : Fin N → Bool) (i : Fin N) :
    (((orientedPairOrder A o)
      (blockPosition 2 N i (0 : Fin 2)) : M.E) : α) =
      A.element i (o i) := by
  rfl

@[simp] theorem orientedPairOrder_block_one
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN)
    (o : Fin N → Bool) (i : Fin N) :
    (((orientedPairOrder A o)
      (blockPosition 2 N i (1 : Fin 2)) : M.E) : α) =
      A.element i (Bool.not (o i)) := by
  cases hoi : o i <;> rfl

private theorem pair_zero_add_one
    {N : ℕ} (hN : 0 < N) (i : Fin N) :
    cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (blockPosition 2 N i (0 : Fin 2)) 1 =
      blockPosition 2 N i (1 : Fin 2) := by
  simpa using
    cyclicIndex_blockPosition_same 2 N (by omega) hN
      i (0 : Fin 2) 1 (by omega)

private theorem pair_one_add_one
    {N : ℕ} (hN : 0 < N) (i : Fin N) :
    cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (blockPosition 2 N i (1 : Fin 2)) 1 =
      blockPosition 2 N (cyclicIndex N hN i 1) (0 : Fin 2) := by
  simpa using
    cyclicIndex_blockPosition_next 2 N (by omega) hN
      i (1 : Fin 2) 1 (by omega) (by omega)

private theorem pair_zero_add_two
    {N : ℕ} (hN : 0 < N) (i : Fin N) :
    cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (blockPosition 2 N i (0 : Fin 2)) 2 =
      blockPosition 2 N (cyclicIndex N hN i 1) (0 : Fin 2) := by
  calc
    cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (blockPosition 2 N i (0 : Fin 2)) 2 =
      cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
          (blockPosition 2 N i (0 : Fin 2)) 1) 1 := by
            symm
            simpa using
              cyclicIndex_add (2 * N) (Nat.mul_pos (by omega) hN)
                (blockPosition 2 N i (0 : Fin 2)) 1 1
    _ = cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (blockPosition 2 N i (1 : Fin 2)) 1 := by
          rw [pair_zero_add_one hN i]
    _ = blockPosition 2 N (cyclicIndex N hN i 1) (0 : Fin 2) :=
      pair_one_add_one hN i

private theorem pair_zero_add_three
    {N : ℕ} (hN : 0 < N) (i : Fin N) :
    cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (blockPosition 2 N i (0 : Fin 2)) 3 =
      blockPosition 2 N (cyclicIndex N hN i 1) (1 : Fin 2) := by
  calc
    cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (blockPosition 2 N i (0 : Fin 2)) 3 =
      cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
          (blockPosition 2 N i (0 : Fin 2)) 2) 1 := by
            symm
            simpa using
              cyclicIndex_add (2 * N) (Nat.mul_pos (by omega) hN)
                (blockPosition 2 N i (0 : Fin 2)) 2 1
    _ = cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (blockPosition 2 N (cyclicIndex N hN i 1) (0 : Fin 2)) 1 := by
          rw [pair_zero_add_two hN i]
    _ = blockPosition 2 N (cyclicIndex N hN i 1) (1 : Fin 2) :=
      pair_zero_add_one hN (cyclicIndex N hN i 1)

private theorem pair_one_add_two
    {N : ℕ} (hN : 0 < N) (i : Fin N) :
    cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (blockPosition 2 N i (1 : Fin 2)) 2 =
      blockPosition 2 N (cyclicIndex N hN i 1) (1 : Fin 2) := by
  calc
    cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (blockPosition 2 N i (1 : Fin 2)) 2 =
      cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
          (blockPosition 2 N i (1 : Fin 2)) 1) 1 := by
            symm
            simpa using
              cyclicIndex_add (2 * N) (Nat.mul_pos (by omega) hN)
                (blockPosition 2 N i (1 : Fin 2)) 1 1
    _ = cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (blockPosition 2 N (cyclicIndex N hN i 1) (0 : Fin 2)) 1 := by
          rw [pair_one_add_one hN i]
    _ = blockPosition 2 N (cyclicIndex N hN i 1) (1 : Fin 2) :=
      pair_zero_add_one hN (cyclicIndex N hN i 1)

private theorem pair_one_add_three
    {N : ℕ} (hN : 0 < N) (i : Fin N) :
    cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (blockPosition 2 N i (1 : Fin 2)) 3 =
      blockPosition 2 N (cyclicIndex N hN i 2) (0 : Fin 2) := by
  calc
    cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (blockPosition 2 N i (1 : Fin 2)) 3 =
      cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
          (blockPosition 2 N i (1 : Fin 2)) 2) 1 := by
            symm
            simpa using
              cyclicIndex_add (2 * N) (Nat.mul_pos (by omega) hN)
                (blockPosition 2 N i (1 : Fin 2)) 2 1
    _ = cyclicIndex (2 * N) (Nat.mul_pos (by omega) hN)
        (blockPosition 2 N (cyclicIndex N hN i 1) (1 : Fin 2)) 1 := by
          rw [pair_one_add_two hN i]
    _ = blockPosition 2 N
        (cyclicIndex N hN (cyclicIndex N hN i 1) 1) (0 : Fin 2) :=
      pair_one_add_one hN (cyclicIndex N hN i 1)
    _ = blockPosition 2 N (cyclicIndex N hN i 2) (0 : Fin 2) := by
      simpa using cyclicIndex_add N hN i 1 1

private theorem left_bitPick_eq_last
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN)
    (o : Fin N → Bool) (i : Fin N) :
    bitPick (A.element i true) (A.element i false) (o i) =
      A.element i (Bool.not (o i)) := by
  cases hoi : o i <;> simp [bitPick, hoi]

private theorem right_bitPick_eq_first
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN)
    (o : Fin N → Bool) (i : Fin N) :
    bitPick (A.element i false) (A.element i true) (o i) =
      A.element i (o i) := by
  cases hoi : o i <;> simp [bitPick, hoi]

/-- A rank-four window beginning at a pair boundary is exactly the aligned
two-pair window, independently of the orientations inside the pairs. -/
theorem cyclicWindow_orientedPairOrder_aligned
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN)
    (h2N : 2 < N) (o : Fin N → Bool) (i : Fin N) :
    cyclicWindow 4 (Nat.mul_pos (by omega) hN) (orientedPairOrder A o)
        (blockPosition 2 N i (0 : Fin 2)) =
      A.window i := by
  rw [← A.block_union_core_eq_window (by omega) i,
    Rank4GcdTwoRepair.core_eq_next_block A i]
  ext x
  simp only [cyclicWindow, Set.mem_range, Set.mem_union,
    AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j
    · cases hoi : o i
      · exact Or.inl (Or.inl (by simp [hoi]))
      · exact Or.inl (Or.inr (by simp [hoi]))
    · cases hoi : o i
      · exact Or.inl (Or.inr (by simp [pair_zero_add_one hN i, hoi]))
      · exact Or.inl (Or.inl (by simp [pair_zero_add_one hN i, hoi]))
    · cases hoj : o (cyclicIndex N hN i 1)
      · exact Or.inr (Or.inl (by simp [pair_zero_add_two hN i, hoj]))
      · exact Or.inr (Or.inr (by simp [pair_zero_add_two hN i, hoj]))
    · cases hoj : o (cyclicIndex N hN i 1)
      · exact Or.inr (Or.inr (by simp [pair_zero_add_three hN i, hoj]))
      · exact Or.inr (Or.inl (by simp [pair_zero_add_three hN i, hoj]))
  · intro hx
    rcases hx with ((hx | hx) | (hx | hx))
    · subst x
      cases hoi : o i
      · exact ⟨0, by simp [hoi]⟩
      · exact ⟨1, by simp [pair_zero_add_one hN i, hoi]⟩
    · subst x
      cases hoi : o i
      · exact ⟨1, by simp [pair_zero_add_one hN i, hoi]⟩
      · exact ⟨0, by simp [hoi]⟩
    · subst x
      cases hoj : o (cyclicIndex N hN i 1)
      · exact ⟨2, by simp [pair_zero_add_two hN i, hoj]⟩
      · exact ⟨3, by simp [pair_zero_add_three hN i, hoj]⟩
    · subst x
      cases hoj : o (cyclicIndex N hN i 1)
      · exact ⟨3, by simp [pair_zero_add_three hN i, hoj]⟩
      · exact ⟨2, by simp [pair_zero_add_two hN i, hoj]⟩

/-- A rank-four window beginning in the second slot of a pair is exactly the
shifted-window set controlled by the local Boolean relation. -/
theorem cyclicWindow_orientedPairOrder_shifted
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN)
    (h2N : 2 < N) (o : Fin N → Bool) (i : Fin N) :
    cyclicWindow 4 (Nat.mul_pos (by omega) hN) (orientedPairOrder A o)
        (blockPosition 2 N i (1 : Fin 2)) =
      ({bitPick (A.element i true) (A.element i false) (o i),
        bitPick
          (A.element (cyclicIndex N hN i 2) false)
          (A.element (cyclicIndex N hN i 2) true)
          (o (cyclicIndex N hN i 2))} ∪ A.core i : Set α) := by
  rw [left_bitPick_eq_last A o i,
    right_bitPick_eq_first A o (cyclicIndex N hN i 2),
    Rank4GcdTwoRepair.core_eq_next_block A i]
  ext x
  simp only [cyclicWindow, Set.mem_range, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff,
    AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j
    · exact Or.inl (Or.inl (by simp))
    · cases hoj : o (cyclicIndex N hN i 1)
      · exact Or.inr (Or.inl (by simp [pair_one_add_one hN i, hoj]))
      · exact Or.inr (Or.inr (by simp [pair_one_add_one hN i, hoj]))
    · cases hoj : o (cyclicIndex N hN i 1)
      · exact Or.inr (Or.inr (by simp [pair_one_add_two hN i, hoj]))
      · exact Or.inr (Or.inl (by simp [pair_one_add_two hN i, hoj]))
    · exact Or.inl (Or.inr (by simp [pair_one_add_three hN i]))
  · intro hx
    rcases hx with ((hx | hx) | (hx | hx))
    · subst x
      exact ⟨0, by simp⟩
    · subst x
      exact ⟨3, by simp [pair_one_add_three hN i]⟩
    · subst x
      cases hoj : o (cyclicIndex N hN i 1)
      · exact ⟨1, by simp [pair_one_add_one hN i, hoj]⟩
      · exact ⟨2, by simp [pair_one_add_two hN i, hoj]⟩
    · subst x
      cases hoj : o (cyclicIndex N hN i 1)
      · exact ⟨2, by simp [pair_one_add_two hN i, hoj]⟩
      · exact ⟨1, by simp [pair_one_add_one hN i, hoj]⟩

/-- An explicit satisfying orientation of all local pair relations flattens
an admissible rank-four pair cycle to a genuine cyclic basis ordering. -/
theorem cyclicBasisOrder_of_pair_orientation
    {M : Matroid α} {N : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N 2 hN)
    (h2N : 2 < N)
    (o : Fin N → Bool)
    (ho : ∀ i : Fin N,
      A.localRelation (by omega) i (o i)
        (o (cyclicIndex N hN i 2))) :
    CyclicBasisOrder M 4 (Nat.mul_pos (by omega) hN)
      (orientedPairOrder A o) := by
  intro p
  obtain ⟨z, rfl⟩ := (blockPositionEquiv 2 N).surjective p
  rcases z with ⟨i, d⟩
  fin_cases d
  · rw [cyclicWindow_orientedPairOrder_aligned A h2N o i]
    exact A.alignedBase i
  · rw [cyclicWindow_orientedPairOrder_shifted A h2N o i]
    exact (A.shifted_window_iff_localRelation
      (by omega) h2N i (o i) (o (cyclicIndex N hN i 2))).2 (ho i)

end

end Rank4GcdTwoFlattening
end HigherRankKUM
