import HigherRankKUM.AdmissiblePairCycle
import Mathlib.Data.Set.Card

namespace HigherRankKUM
namespace PairBlockPartition

open Set

variable {α : Type*}

/-- A partition of a matroid ground set into labelled two-element blocks,
separated from any basis-window conditions.  This is the combinatorial carrier
underlying `AdmissiblePairCycle.Data`. -/
structure Data (M : Matroid α) (N : ℕ) where
  block : Fin N → Set α
  card_two : ∀ i, (block i).encard = 2
  subset_ground : ∀ i, block i ⊆ M.E
  disjoint : ∀ {i j : Fin N}, i ≠ j → Disjoint (block i) (block j)
  cover : (⋃ i, block i) = M.E

/-- Any set of extended cardinality two can be labelled by `Bool`. -/
noncomputable def boolEquivOfEncardTwo (S : Set α) (hS : S.encard = 2) : Bool ≃ S := by
  classical
  obtain ⟨x, y, hxy, hSxy⟩ := Set.encard_eq_two.mp hS
  rw [hSxy]
  let f : Bool → ({x, y} : Set α) := fun b =>
    match b with
    | false => ⟨x, by simp⟩
    | true => ⟨y, by simp⟩
  apply Equiv.ofBijective f
  constructor
  · intro b c hbc
    cases b <;> cases c
    · rfl
    · exfalso
      exact hxy (congrArg Subtype.val hbc)
    · exfalso
      exact hxy (congrArg Subtype.val hbc).symm
    · rfl
  · rintro ⟨z, hz⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩

namespace Data

variable {M : Matroid α} {N : ℕ} (P : Data M N)

/-- Boolean labelling of one block. -/
noncomputable def label (i : Fin N) : Bool ≃ P.block i :=
  boolEquivOfEncardTwo (P.block i) (P.card_two i)

/-- Coordinate map obtained by labelling every two-element block. -/
noncomputable def coordMap (z : Fin N × Bool) : M.E :=
  ⟨(P.label z.1 z.2).1, P.subset_ground z.1 (P.label z.1 z.2).2⟩

/-- Distinct block coordinates map to distinct ground elements. -/
theorem coordMap_injective : Function.Injective P.coordMap := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  by_cases hij : i = j
  · subst j
    have hlabel : P.label i b = P.label i c :=
      Subtype.ext (congrArg Subtype.val h)
    have hbc : b = c := (P.label i).injective hlabel
    subst c
    rfl
  · exfalso
    have hval : (P.label i b : α) = P.label j c :=
      congrArg Subtype.val h
    have hi : (P.label i b : α) ∈ P.block i := (P.label i b).2
    have hj : (P.label j c : α) ∈ P.block j := (P.label j c).2
    have hj' : (P.label i b : α) ∈ P.block j := by
      rw [hval]
      exact hj
    exact Set.disjoint_left.1 (P.disjoint hij) hi hj'

/-- The coordinate map covers the whole ground set because the blocks do. -/
theorem coordMap_surjective : Function.Surjective P.coordMap := by
  intro x
  have hxUnion : x.1 ∈ ⋃ i, P.block i := by
    rw [P.cover]
    exact x.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxUnion
  obtain ⟨b, hb⟩ := (P.label i).surjective ⟨x.1, hi⟩
  refine ⟨(i, b), ?_⟩
  apply Subtype.ext
  exact congrArg Subtype.val hb

/-- Canonical (up to the noncomputable choices of labels inside blocks)
coordinate equivalence associated to a pair-block partition. -/
noncomputable def pairEquiv : Fin N × Bool ≃ M.E :=
  Equiv.ofBijective P.coordMap ⟨P.coordMap_injective, P.coordMap_surjective⟩

@[simp] theorem pairEquiv_apply_val (i : Fin N) (b : Bool) :
    ((P.pairEquiv (i, b) : M.E) : α) = (P.label i b : α) := rfl

/-- Recovering a pair set from the constructed coordinate equivalence gives
exactly the original block. -/
theorem pairSet_pairEquiv_eq_block (i : Fin N) :
    AdmissiblePairCycle.pairSet P.pairEquiv i = P.block i := by
  change ({(P.label i false : α), (P.label i true : α)} : Set α) = P.block i
  ext x
  constructor
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact (P.label i false).2
    · exact (P.label i true).2
  · intro hx
    obtain ⟨b, hb⟩ := (P.label i).surjective ⟨x, hx⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    cases b
    · exact Or.inl (congrArg Subtype.val hb).symm
    · exact Or.inr (congrArg Subtype.val hb).symm

end Data

/-- Forgetting the basis-window information from an admissible pair cycle
produces its underlying pair-block partition. -/
def ofAdmissiblePairCycle
    {M : Matroid α} {N h : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N h hN) : Data M N where
  block := A.block
  card_two := fun i => by
    rw [AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet]
    exact Set.encard_pair (A.element_ne i)
  subset_ground := A.block_subset_ground
  disjoint := fun hij => A.block_disjoint_of_ne hij
  cover := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact A.block_subset_ground i hi
    · intro hx
      let y : M.E := ⟨x, hx⟩
      let z : Fin N × Bool := A.pairEquiv.symm y
      have hz : A.pairEquiv z = y := A.pairEquiv.apply_symm_apply y
      rcases z with ⟨i, b⟩
      refine Set.mem_iUnion.2 ⟨i, ?_⟩
      simp only [AdmissiblePairCycle.Data.block, AdmissiblePairCycle.pairSet,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      cases b
      · exact Or.inl (congrArg Subtype.val hz).symm
      · exact Or.inr (congrArg Subtype.val hz).symm

end PairBlockPartition
end HigherRankKUM
