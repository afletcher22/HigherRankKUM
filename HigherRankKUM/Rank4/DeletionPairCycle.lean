import HigherRankKUM.PairCycleFromOrder
import HigherRankKUM.CyclicOrder
import Mathlib.Combinatorics.Matroid.Minor.Delete
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4DeletionPairCycle

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- Insert a distinguished ground element in front of an enumeration of the
remaining ground set. -/
def insertGroundEquiv
    (M : Matroid α) (e : α) (he : e ∈ M.E) :
    Option ↥(M.E \ ({e} : Set α)) ≃ M.E := by
  classical
  have hnot : e ∉ M.E \ ({e} : Set α) := by simp
  have hset : insert e (M.E \ ({e} : Set α)) = M.E := by
    ext x
    constructor
    · intro hx
      rcases hx with rfl | hx
      · exact he
      · exact hx.1
    · intro hxE
      by_cases hxe : x = e
      · exact Or.inl hxe
      · exact Or.inr ⟨hxE, by simpa using hxe⟩
  exact
    (Equiv.optionEquivSumPUnit ↥(M.E \ ({e} : Set α))).trans
      ((Equiv.Set.insert hnot).symm.trans (Equiv.setCongr hset))

@[simp] theorem insertGroundEquiv_none
    (M : Matroid α) (e : α) (he : e ∈ M.E) :
    (((insertGroundEquiv M e he) none : M.E) : α) = e := by
  classical
  simp [insertGroundEquiv]

@[simp] theorem insertGroundEquiv_some
    (M : Matroid α) (e : α) (he : e ∈ M.E)
    (x : ↥(M.E \ ({e} : Set α))) :
    (((insertGroundEquiv M e he) (some x) : M.E) : α) = x.1 := by
  classical
  simp [insertGroundEquiv]

/-- Put e at position zero and then list the deletion order. -/
def frontInsertOrder
    {m : ℕ} (M : Matroid α) (e : α) (he : e ∈ M.E)
    (sigma : Fin m ≃ ↥(M.E \ ({e} : Set α))) :
    Fin (m + 1) ≃ M.E :=
  (finSuccEquiv m).trans
    ((Equiv.optionCongr sigma).trans (insertGroundEquiv M e he))

@[simp] theorem frontInsertOrder_zero
    {m : ℕ} (M : Matroid α) (e : α) (he : e ∈ M.E)
    (sigma : Fin m ≃ ↥(M.E \ ({e} : Set α))) :
    (((frontInsertOrder M e he sigma) (0 : Fin (m + 1)) : M.E) : α) = e := by
  simp [frontInsertOrder]

@[simp] theorem frontInsertOrder_succ
    {m : ℕ} (M : Matroid α) (e : α) (he : e ∈ M.E)
    (sigma : Fin m ≃ ↥(M.E \ ({e} : Set α))) (j : Fin m) :
    (((frontInsertOrder M e he sigma) j.succ : M.E) : α) = (sigma j : α) := by
  simp [frontInsertOrder]

/-- The specialization of front insertion to an even full length 2N. -/
def frontInsertPairOrder
    {N : ℕ} (hN : 0 < N)
    (M : Matroid α) (e : α) (he : e ∈ M.E)
    (sigma : Fin (2 * N - 1) ≃ ↥(M.E \ ({e} : Set α))) :
    Fin (2 * N) ≃ M.E :=
  (finCongr (by omega : 2 * N = (2 * N - 1) + 1)).trans
    (frontInsertOrder M e he sigma)

@[simp] theorem frontInsertPairOrder_zero
    {N : ℕ} (hN : 0 < N)
    (M : Matroid α) (e : α) (he : e ∈ M.E)
    (sigma : Fin (2 * N - 1) ≃ ↥(M.E \ ({e} : Set α))) :
    (((frontInsertPairOrder hN M e he sigma) (⟨0, by omega⟩ : Fin (2 * N)) : M.E) : α) = e := by
  simp [frontInsertPairOrder]

/-- Any positive full-order position is the corresponding deletion position
shifted down by one. -/
theorem frontInsertPairOrder_of_pos
    {N : ℕ} (hN : 0 < N)
    (M : Matroid α) (e : α) (he : e ∈ M.E)
    (sigma : Fin (2 * N - 1) ≃ ↥(M.E \ ({e} : Set α)))
    (q : Fin (2 * N)) (hq : 0 < q.val) :
    (((frontInsertPairOrder hN M e he sigma) q : M.E) : α) =
      (sigma ⟨q.val - 1, by omega⟩ : α) := by
  let j : Fin (2 * N - 1) := ⟨q.val - 1, by omega⟩
  have hcast :
      (finCongr (by omega : 2 * N = (2 * N - 1) + 1)) q = j.succ := by
    apply Fin.ext
    dsimp [j]
    omega
  change
    (((frontInsertOrder M e he sigma)
      ((finCongr (by omega : 2 * N = (2 * N - 1) + 1)) q) : M.E) : α) =
      (sigma ⟨q.val - 1, by omega⟩ : α)
  rw [hcast]
  simpa [j] using frontInsertOrder_succ M e he sigma j

@[simp] theorem frontInsertPairOrder_block_zero_zero
    {N : ℕ} (hN : 0 < N)
    (M : Matroid α) (e : α) (he : e ∈ M.E)
    (sigma : Fin (2 * N - 1) ≃ ↥(M.E \ ({e} : Set α))) :
    (((frontInsertPairOrder hN M e he sigma)
      (blockPosition 2 N (⟨0, hN⟩ : Fin N) (0 : Fin 2)) : M.E) : α) = e := by
  have hpos :
      blockPosition 2 N (⟨0, hN⟩ : Fin N) (0 : Fin 2) = (⟨0, by omega⟩ : Fin (2 * N)) := by
    apply Fin.ext
    simp
  rw [hpos]
  exact frontInsertPairOrder_zero hN M e he sigma

@[simp] theorem frontInsertPairOrder_block_one
    {N : ℕ} (hN : 0 < N)
    (M : Matroid α) (e : α) (he : e ∈ M.E)
    (sigma : Fin (2 * N - 1) ≃ ↥(M.E \ ({e} : Set α)))
    (i : Fin N) :
    (((frontInsertPairOrder hN M e he sigma)
      (blockPosition 2 N i (1 : Fin 2)) : M.E) : α) =
      (sigma ⟨2 * i.val, by omega⟩ : α) := by
  have hq :
      0 < (blockPosition 2 N i (1 : Fin 2)).val := by
    simp [blockPosition_val]
  rw [frontInsertPairOrder_of_pos hN M e he sigma _ hq]
  have hidx :
      (⟨(blockPosition 2 N i (1 : Fin 2)).val - 1, by omega⟩ :
        Fin (2 * N - 1)) = ⟨2 * i.val, by omega⟩ := by
    apply Fin.ext
    simp [blockPosition_val]
  rw [hidx]

theorem frontInsertPairOrder_block_zero_of_pos
    {N : ℕ} (hN : 0 < N)
    (M : Matroid α) (e : α) (he : e ∈ M.E)
    (sigma : Fin (2 * N - 1) ≃ ↥(M.E \ ({e} : Set α)))
    (i : Fin N) (hi : 0 < i.val) :
    (((frontInsertPairOrder hN M e he sigma)
      (blockPosition 2 N i (0 : Fin 2)) : M.E) : α) =
      (sigma ⟨2 * i.val - 1, by omega⟩ : α) := by
  have hq :
      0 < (blockPosition 2 N i (0 : Fin 2)).val := by
    simp [blockPosition_val]
    omega
  rw [frontInsertPairOrder_of_pos hN M e he sigma _ hq]
  have hidx :
      (⟨(blockPosition 2 N i (0 : Fin 2)).val - 1, by omega⟩ :
        Fin (2 * N - 1)) = ⟨2 * i.val - 1, by omega⟩ := by
    apply Fin.ext
    simp [blockPosition_val]
  rw [hidx]

/-- A nonwrapping four-window is the explicit four-element set at offsets
0,1,2,3. -/
theorem cyclicWindow_four_no_wrap
    {E : Set α} {m : ℕ} (hm : 0 < m)
    (sigma : Fin m ≃ E) (s : ℕ) (hs : s + 3 < m) :
    cyclicWindow 4 hm sigma ⟨s, by omega⟩ =
      ({(sigma ⟨s, by omega⟩ : α),
        (sigma ⟨s + 1, by omega⟩ : α),
        (sigma ⟨s + 2, by omega⟩ : α),
        (sigma ⟨s + 3, by omega⟩ : α)} : Set α) := by
  have hidx0 :
      cyclicIndex m hm ⟨s, by omega⟩ 0 = ⟨s, by omega⟩ := by
    apply Fin.ext
    simp [cyclicIndex_val, Nat.mod_eq_of_lt (by omega : s < m)]
  have hidx1 :
      cyclicIndex m hm ⟨s, by omega⟩ 1 = ⟨s + 1, by omega⟩ := by
    apply Fin.ext
    simp [cyclicIndex_val, Nat.mod_eq_of_lt (by omega : s + 1 < m)]
  have hidx2 :
      cyclicIndex m hm ⟨s, by omega⟩ 2 = ⟨s + 2, by omega⟩ := by
    apply Fin.ext
    simp [cyclicIndex_val, Nat.mod_eq_of_lt (by omega : s + 2 < m)]
  have hidx3 :
      cyclicIndex m hm ⟨s, by omega⟩ 3 = ⟨s + 3, hs⟩ := by
    apply Fin.ext
    simp [cyclicIndex_val, Nat.mod_eq_of_lt hs]
  ext x
  simp only [cyclicWindow, Set.mem_range, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j
    · exact Or.inl (by simpa [hidx0])
    · exact Or.inr (Or.inl (by simpa [hidx1]))
    · exact Or.inr (Or.inr (Or.inl (by simpa [hidx2])))
    · exact Or.inr (Or.inr (Or.inr (by simpa [hidx3])))
  · intro hx
    rcases hx with h | h | h | h
    · exact ⟨0, by simpa [hidx0] using h.symm⟩
    · exact ⟨1, by simpa [hidx1] using h.symm⟩
    · exact ⟨2, by simpa [hidx2] using h.symm⟩
    · exact ⟨3, by simpa [hidx3] using h.symm⟩

/-- For a non-boundary pair block, its union with the next block in the
front-inserted order is exactly a four-window of the deletion order. -/
theorem interior_pair_union_eq_deletion_window
    {N : ℕ} (hN : 0 < N)
    (M : Matroid α) (e : α) (he : e ∈ M.E)
    (sigma : Fin (2 * N - 1) ≃ ↥(M.E \ ({e} : Set α)))
    (i : Fin N) (hi0 : 0 < i.val) (hinext : i.val + 1 < N) :
    ({((frontInsertPairOrder hN M e he sigma)
          (blockPosition 2 N i (0 : Fin 2)) : M.E).1,
      ((frontInsertPairOrder hN M e he sigma)
          (blockPosition 2 N i (1 : Fin 2)) : M.E).1,
      ((frontInsertPairOrder hN M e he sigma)
          (blockPosition 2 N (cyclicIndex N hN i 1)
            (0 : Fin 2)) : M.E).1,
      ((frontInsertPairOrder hN M e he sigma)
          (blockPosition 2 N (cyclicIndex N hN i 1)
            (1 : Fin 2)) : M.E).1} : Set α) =
      cyclicWindow 4 (by omega : 0 < 2 * N - 1) sigma
        ⟨2 * i.val - 1, by omega⟩ := by
  have hnext :
      cyclicIndex N hN i 1 = ⟨i.val + 1, hinext⟩ := by
    apply Fin.ext
    simp only [cyclicIndex_val]
    rw [Nat.mod_eq_of_lt hinext]
  rw [hnext]
  rw [frontInsertPairOrder_block_zero_of_pos hN M e he sigma i hi0]
  rw [frontInsertPairOrder_block_one hN M e he sigma i]
  have hnextPos : 0 < (⟨i.val + 1, hinext⟩ : Fin N).val := by
    exact Nat.zero_lt_succ i.val
  rw [frontInsertPairOrder_block_zero_of_pos hN M e he sigma
    ⟨i.val + 1, hinext⟩ hnextPos]
  rw [frontInsertPairOrder_block_one hN M e he sigma
    ⟨i.val + 1, hinext⟩]
  let t : ℕ := i.val - 1
  have hit : i.val = t + 1 := by
    dsimp [t]
    omega
  rw [hit]
  have hs : (2 * t + 1) + 3 < 2 * N - 1 := by
    omega
  have hstart :
      (⟨2 * (t + 1) - 1, by omega⟩ : Fin (2 * N - 1)) =
        ⟨2 * t + 1, by omega⟩ := by
    apply Fin.ext
    omega
  rw [hstart]
  rw [cyclicWindow_four_no_wrap
    (by omega : 0 < 2 * N - 1) sigma (2 * t + 1) hs]
  have hidx1 :
      (⟨2 * (t + 1), by omega⟩ : Fin (2 * N - 1)) =
        ⟨2 * t + 2, by omega⟩ := by
    apply Fin.ext
    omega
  have hidx2 :
      (⟨2 * (t + 1 + 1) - 1, by omega⟩ : Fin (2 * N - 1)) =
        ⟨2 * t + 3, by omega⟩ := by
    apply Fin.ext
    omega
  have hidx3 :
      (⟨2 * (t + 1 + 1), by omega⟩ : Fin (2 * N - 1)) =
        ⟨2 * t + 4, by omega⟩ := by
    apply Fin.ext
    omega
  rw [hidx1, hidx2, hidx3]

/-- Interior aligned pair windows of a front-inserted deletion CBO remain
bases of the original matroid whenever the deleted singleton is coindependent. -/
theorem interior_pair_union_isBase
    {N : ℕ} (hN : 0 < N)
    (M : Matroid α) (e : α) (he : e ∈ M.E)
    (hco : M.Coindep ({e} : Set α))
    (sigma : Fin (2 * N - 1) ≃ ↥(M.E \ ({e} : Set α)))
    (hCBO : CyclicBasisOrder (M ＼ ({e} : Set α)) 4
      (by omega : 0 < 2 * N - 1) sigma)
    (i : Fin N) (hi0 : 0 < i.val) (hinext : i.val + 1 < N) :
    M.IsBase
      ({((frontInsertPairOrder hN M e he sigma)
          (blockPosition 2 N i (0 : Fin 2)) : M.E).1,
        ((frontInsertPairOrder hN M e he sigma)
          (blockPosition 2 N i (1 : Fin 2)) : M.E).1,
        ((frontInsertPairOrder hN M e he sigma)
          (blockPosition 2 N (cyclicIndex N hN i 1)
            (0 : Fin 2)) : M.E).1,
        ((frontInsertPairOrder hN M e he sigma)
          (blockPosition 2 N (cyclicIndex N hN i 1)
            (1 : Fin 2)) : M.E).1} : Set α) := by
  rw [interior_pair_union_eq_deletion_window hN M e he sigma i hi0 hinext]
  exact (hco.delete_isBase_iff.mp
    (hCBO ⟨2 * i.val - 1, by omega⟩)).1

end

end Rank4DeletionPairCycle
end HigherRankKUM
