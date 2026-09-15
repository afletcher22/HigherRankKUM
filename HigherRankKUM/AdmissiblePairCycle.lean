import HigherRankKUM.PairCycle
import HigherRankKUM.PairCycleIndexing

namespace HigherRankKUM
namespace AdmissiblePairCycle

open Set
open PairCycle
open PairCycleIndexing
open BinaryRelationCycle

variable {α : Type*}

/-- The ground element in block `i` with Boolean label `b`. -/
def elem {M : Matroid α} {N : ℕ}
    (e : Fin N × Bool ≃ M.E) (i : Fin N) (b : Bool) : α :=
  (e (i, b) : M.E).1

/-- One labelled two-element block. -/
def pairSet {M : Matroid α} {N : ℕ}
    (e : Fin N × Bool ≃ M.E) (i : Fin N) : Set α :=
  {elem e i false, elem e i true}

/-- The union of `h` cyclically consecutive pair blocks. -/
def alignedWindow {M : Matroid α} {N h : ℕ} (hN : 0 < N)
    (e : Fin N × Bool ≃ M.E) (i : Fin N) : Set α :=
  Set.range fun z : Fin h × Bool =>
    elem e (cyclicIndex N hN i z.1.val) z.2

/-- Exact formal package for the arbitrary-rank gcd-two setup.  The equivalence
encodes a partition of the ground set into `N` labelled pairs, and
`alignedBase` is precisely the assertion that every `h` consecutive pairs
have basis union.  The size and rank equations are retained explicitly so the
formal statement mirrors `|E|=2N`, `r=2h`. -/
structure Data (M : Matroid α) (N h : ℕ) (hN : 0 < N) where
  pairEquiv : Fin N × Bool ≃ M.E
  groundSize : M.E.encard = ((2 * N : ℕ) : ℕ∞)
  rankEq : M.eRank = ((2 * h : ℕ) : ℕ∞)
  alignedBase : ∀ i : Fin N, M.IsBase (alignedWindow (h := h) hN pairEquiv i)

namespace Data

variable {M : Matroid α} {N h : ℕ} {hN : 0 < N}
    (A : Data M N h hN)

abbrev element (i : Fin N) (b : Bool) : α := elem A.pairEquiv i b

abbrev block (i : Fin N) : Set α := pairSet A.pairEquiv i

abbrev window (i : Fin N) : Set α := alignedWindow (h := h) hN A.pairEquiv i

/-- The `h-1` complete pair blocks strictly between the two endpoint pairs of
a shifted rank window. -/
def core (i : Fin N) : Set α :=
  Set.range fun z : Fin (h - 1) × Bool =>
    A.element (cyclicIndex N hN i (z.1.val + 1)) z.2

lemma element_mem_ground (i : Fin N) (b : Bool) : A.element i b ∈ M.E :=
  (A.pairEquiv (i, b)).2

lemma element_injective :
    Function.Injective (fun z : Fin N × Bool => A.element z.1 z.2) := by
  intro x y hxy
  apply A.pairEquiv.injective
  apply Subtype.ext
  exact hxy

lemma element_ne (i : Fin N) : A.element i false ≠ A.element i true := by
  intro h
  have hp : (i, false) = (i, true) := A.element_injective h
  exact Bool.false_ne_true (congrArg Prod.snd hp)

lemma block_subset_ground (i : Fin N) : A.block i ⊆ M.E := by
  intro x hx
  simp only [block, pairSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact A.element_mem_ground _ _
  · exact A.element_mem_ground _ _

lemma block_disjoint_of_ne {i j : Fin N} (hij : i ≠ j) :
    Disjoint (A.block i) (A.block j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  simp only [block, pairSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hxi hxj
  rcases hxi with rfl | rfl <;> rcases hxj with h | h
  · have hp : (i, false) = (j, false) := A.element_injective h
    exact hij (congrArg Prod.fst hp)
  · have hp : (i, false) = (j, true) := A.element_injective h
    exact hij (congrArg Prod.fst hp)
  · have hp : (i, true) = (j, false) := A.element_injective h
    exact hij (congrArg Prod.fst hp)
  · have hp : (i, true) = (j, true) := A.element_injective h
    exact hij (congrArg Prod.fst hp)

lemma block_subset_window (hh : 0 < h) (i : Fin N) :
    A.block i ⊆ A.window i := by
  intro x hx
  simp only [block, pairSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · refine ⟨(⟨0, hh⟩, false), ?_⟩
    simp [window, alignedWindow]
  · refine ⟨(⟨0, hh⟩, true), ?_⟩
    simp [window, alignedWindow]

lemma core_subset_window (hh : 0 < h) (i : Fin N) :
    A.core i ⊆ A.window i := by
  rintro x ⟨z, rfl⟩
  refine ⟨(⟨z.1.val + 1, by omega⟩, z.2), rfl⟩

lemma block_union_core_eq_window (hh : 0 < h) (i : Fin N) :
    A.block i ∪ A.core i = A.window i := by
  apply Set.Subset.antisymm
  · exact Set.union_subset (A.block_subset_window hh i) (A.core_subset_window hh i)
  · rintro x ⟨z, rfl⟩
    by_cases hz : z.1.val = 0
    · left
      change A.element (cyclicIndex N hN i z.1.val) z.2 ∈ A.block i
      have hidx : cyclicIndex N hN i z.1.val = i := by
        rw [hz]
        exact cyclicIndex_zero N hN i
      rw [hidx]
      cases z.2 <;> simp [block, pairSet]
    · right
      let j : Fin (h - 1) := ⟨z.1.val - 1, by omega⟩
      refine ⟨(j, z.2), ?_⟩
      change A.element (cyclicIndex N hN i (j.val + 1)) z.2 =
        A.element (cyclicIndex N hN i z.1.val) z.2
      apply congrArg (fun t : Fin N => A.element t z.2)
      congr 1
      simp [j]
      omega

lemma core_indep (hh : 0 < h) (i : Fin N) : M.Indep (A.core i) :=
  (A.alignedBase i).indep.subset (A.core_subset_window hh i)

lemma endpoint_index_ne (hh : 0 < h) (hhN : h < N) (i : Fin N) :
    cyclicIndex N hN i h ≠ i :=
  cyclicIndex_ne_self_of_pos_of_lt N hN i hh hhN

lemma endpoint_blocks_disjoint (hh : 0 < h) (hhN : h < N) (i : Fin N) :
    Disjoint (A.block i) (A.block (cyclicIndex N hN i h)) :=
  A.block_disjoint_of_ne
    (endpoint_index_ne (N := N) (h := h) (hN := hN) hh hhN i).symm

lemma block_disjoint_core (hh : 0 < h) (hhN : h < N) (i : Fin N) :
    Disjoint (A.block i) (A.core i) := by
  rw [Set.disjoint_left]
  intro x hx hc
  simp only [block, pairSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  obtain ⟨z, hzx⟩ := hc
  rcases hx with rfl | rfl
  · have hp : (i, false) = (cyclicIndex N hN i (z.1.val + 1), z.2) :=
      A.element_injective (by simpa using hzx.symm)
    have hi := congrArg Prod.fst hp
    have hoff : z.1.val + 1 < N := by omega
    exact (cyclicIndex_ne_self_of_pos_of_lt N hN i (by omega) hoff) hi.symm
  · have hp : (i, true) = (cyclicIndex N hN i (z.1.val + 1), z.2) :=
      A.element_injective (by simpa using hzx.symm)
    have hi := congrArg Prod.fst hp
    have hoff : z.1.val + 1 < N := by omega
    exact (cyclicIndex_ne_self_of_pos_of_lt N hN i (by omega) hoff) hi.symm

lemma endpoint_block_disjoint_core (hh : 0 < h) (hhN : h < N) (i : Fin N) :
    Disjoint (A.block (cyclicIndex N hN i h)) (A.core i) := by
  rw [Set.disjoint_left]
  intro x hx hc
  simp only [block, pairSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  obtain ⟨z, hzx⟩ := hc
  rcases hx with rfl | rfl
  · have hp :
        (cyclicIndex N hN i h, false) =
          (cyclicIndex N hN i (z.1.val + 1), z.2) :=
      A.element_injective (by simpa using hzx.symm)
    have hi := congrArg Prod.fst hp
    have heq := cyclicIndex_injective_offsets N hN i hhN (by omega) hi
    omega
  · have hp :
        (cyclicIndex N hN i h, true) =
          (cyclicIndex N hN i (z.1.val + 1), z.2) :=
      A.element_injective (by simpa using hzx.symm)
    have hi := congrArg Prod.fst hp
    have heq := cyclicIndex_injective_offsets N hN i hhN (by omega) hi
    omega

lemma core_subset_next_window (hh : 0 < h) (i : Fin N) :
    A.core i ⊆ A.window (cyclicIndex N hN i 1) := by
  rintro x ⟨z, rfl⟩
  refine ⟨(⟨z.1.val, by omega⟩, z.2), ?_⟩
  change A.element
      (cyclicIndex N hN (cyclicIndex N hN i 1) z.1.val) z.2 =
    A.element (cyclicIndex N hN i (z.1.val + 1)) z.2
  apply congrArg (fun t : Fin N => A.element t z.2)
  rw [cyclicIndex_add]
  congr 1
  omega

lemma endpoint_block_subset_next_window (hh : 0 < h) (i : Fin N) :
    A.block (cyclicIndex N hN i h) ⊆ A.window (cyclicIndex N hN i 1) := by
  intro x hx
  simp only [block, pairSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hpred : h - 1 < h := by omega
  rcases hx with rfl | rfl
  · refine ⟨(⟨h - 1, hpred⟩, false), ?_⟩
    change A.element
        (cyclicIndex N hN (cyclicIndex N hN i 1) (h - 1)) false =
      A.element (cyclicIndex N hN i h) false
    apply congrArg (fun t : Fin N => A.element t false)
    rw [cyclicIndex_add]
    congr 1
    omega
  · refine ⟨(⟨h - 1, hpred⟩, true), ?_⟩
    change A.element
        (cyclicIndex N hN (cyclicIndex N hN i 1) (h - 1)) true =
      A.element (cyclicIndex N hN i h) true
    apply congrArg (fun t : Fin N => A.element t true)
    rw [cyclicIndex_add]
    congr 1
    omega

lemma endpoint_block_union_core_eq_next_window
    (hh : 0 < h) (i : Fin N) :
    A.block (cyclicIndex N hN i h) ∪ A.core i =
      A.window (cyclicIndex N hN i 1) := by
  apply Set.Subset.antisymm
  · exact Set.union_subset (A.endpoint_block_subset_next_window hh i)
      (A.core_subset_next_window hh i)
  · rintro x ⟨z, rfl⟩
    by_cases hz : z.1.val = h - 1
    · left
      change A.element
          (cyclicIndex N hN (cyclicIndex N hN i 1) z.1.val) z.2 ∈
        A.block (cyclicIndex N hN i h)
      have hidx :
          cyclicIndex N hN (cyclicIndex N hN i 1) z.1.val =
            cyclicIndex N hN i h := by
        rw [hz, cyclicIndex_add]
        congr 1
        omega
      rw [hidx]
      cases z.2 <;> simp [block, pairSet]
    · right
      let j : Fin (h - 1) := ⟨z.1.val, by omega⟩
      refine ⟨(j, z.2), ?_⟩
      change A.element (cyclicIndex N hN i (j.val + 1)) z.2 =
        A.element (cyclicIndex N hN (cyclicIndex N hN i 1) z.1.val) z.2
      apply congrArg (fun t : Fin N => A.element t z.2)
      rw [cyclicIndex_add]
      congr 1
      simp [j]
      omega

lemma endpoint_basis_left (hh : 0 < h) (i : Fin N) :
    M.IsBase (A.block i ∪ A.core i) := by
  rw [A.block_union_core_eq_window hh i]
  exact A.alignedBase i

lemma endpoint_basis_right (hh : 0 < h) (i : Fin N) :
    M.IsBase (A.block (cyclicIndex N hN i h) ∪ A.core i) := by
  rw [A.endpoint_block_union_core_eq_next_window hh i]
  exact A.alignedBase (cyclicIndex N hN i 1)

/-- The shifted-window compatibility relation for the pair cycle.  The left
labels are reversed because an orientation bit chooses the first element of a
pair while the shifted window uses the last element of the left pair. -/
def localRelation (hh : 0 < h) (i : Fin N) : Relation :=
  crossBaseRelation (M.contract (A.core i))
    (A.element i true) (A.element i false)
    (A.element (cyclicIndex N hN i h) false)
    (A.element (cyclicIndex N hN i h) true)

/-- Every local orientation relation arising from an admissible pair cycle has
full support. -/
theorem localRelation_fullSupport
    (hh : 0 < h) (hhN : h < N) (i : Fin N) :
    FullSupport (A.localRelation hh i) := by
  have hleftNe : A.element i true ≠ A.element i false := (A.element_ne i).symm
  have hrightNe :
      A.element (cyclicIndex N hN i h) false ≠
        A.element (cyclicIndex N hN i h) true :=
    A.element_ne (cyclicIndex N hN i h)
  have hblocks := A.endpoint_blocks_disjoint hh hhN i
  have hAB : Disjoint
      ({A.element i true, A.element i false} : Set α)
      {A.element (cyclicIndex N hN i h) false,
        A.element (cyclicIndex N hN i h) true} := by
    simpa [block, pairSet, Set.pair_comm] using hblocks
  have hAC : Disjoint ({A.element i true, A.element i false} : Set α) (A.core i) := by
    simpa [block, pairSet, Set.pair_comm] using A.block_disjoint_core hh hhN i
  have hBC : Disjoint
      ({A.element (cyclicIndex N hN i h) false,
        A.element (cyclicIndex N hN i h) true} : Set α) (A.core i) := by
    simpa [block, pairSet] using A.endpoint_block_disjoint_core hh hhN i
  have hA : M.IsBase ({A.element i true, A.element i false} ∪ A.core i) := by
    simpa [block, pairSet, Set.pair_comm] using A.endpoint_basis_left hh i
  have hB : M.IsBase
      ({A.element (cyclicIndex N hN i h) false,
        A.element (cyclicIndex N hN i h) true} ∪ A.core i) := by
    simpa [block, pairSet] using A.endpoint_basis_right hh i
  exact contracted_endpoint_relation_fullSupport M hleftNe hrightNe hAB
    (A.core_indep hh i) hAC hBC hA hB

/-- Validity of the shifted rank window is exactly the local Boolean relation. -/
theorem shifted_window_iff_localRelation
    (hh : 0 < h) (hhN : h < N) (i : Fin N) (x y : Bool) :
    M.IsBase
      ({bitPick (A.element i true) (A.element i false) x,
        bitPick (A.element (cyclicIndex N hN i h) false)
          (A.element (cyclicIndex N hN i h) true) y} ∪ A.core i) ↔
    A.localRelation hh i x y := by
  apply shifted_window_iff_crossBaseRelation M (A.core_indep hh i)
  intro x' y'
  have hAC := A.block_disjoint_core hh hhN i
  have hBC := A.endpoint_block_disjoint_core hh hhN i
  rw [Set.disjoint_left]
  intro z hz hzc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact Set.disjoint_left.1 hAC (by
      cases x' <;> simp [block, pairSet, bitPick]) hzc
  · exact Set.disjoint_left.1 hBC (by
      cases y' <;> simp [block, pairSet, bitPick]) hzc

end Data
end AdmissiblePairCycle
end HigherRankKUM
