import HigherRankKUM.Density
import HigherRankKUM.LowRank.RankTwo.FinitePartition
import Mathlib.Combinatorics.Matroid.Rank.ENat

namespace HigherRankKUM.RankTwo

open Set

noncomputable section

variable {α : Type*}

/-- Ground elements are equivalent when their singleton closures agree. -/
def closureSetoid (M : Matroid α) : Setoid M.E where
  r e f :=
    M.closure ({(e : α)} : Set α) = M.closure ({(f : α)} : Set α)
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }

/-- The finite partition of the ground set into singleton-closure classes. -/
def closureFinpartition
    (M : Matroid α) [Fintype M.E] [DecidableEq M.E] :
    Finpartition (Finset.univ : Finset M.E) := by
  classical
  exact Finpartition.ofSetoid (closureSetoid M)

@[simp] theorem mem_closureFinpartition_part_iff
    (M : Matroid α) [Fintype M.E] [DecidableEq M.E]
    (e f : M.E) :
    f ∈ (closureFinpartition M).part e ↔
      M.closure ({(e : α)} : Set α) = M.closure ({(f : α)} : Set α) := by
  classical
  exact Finpartition.mem_part_ofSetoid_iff_rel

/-- A finite independent pair of distinct elements is a base in rank two. -/
theorem pair_isBase_of_indep_of_eRank_eq_two
    (M : Matroid α) (hRank : M.eRank = 2)
    {e f : α} (hef : e ≠ f) (hpair : M.Indep ({e, f} : Set α)) :
    M.IsBase ({e, f} : Set α) := by
  apply hpair.isBase_of_eRk_ge (Set.toFinite {e, f})
  rw [hRank, hpair.eRk_eq_encard, Set.encard_pair hef]

/-- Different singleton-closure classes form an independent pair in a loopless matroid. -/
theorem pair_indep_of_closure_ne
    (M : Matroid α) (hLoopless : M.Loopless)
    {e f : α} (he : e ∈ M.E) (hf : f ∈ M.E)
    (hclosure :
      M.closure ({e} : Set α) ≠ M.closure ({f} : Set α)) :
    M.Indep ({e, f} : Set α) := by
  let : M.Loopless := hLoopless
  have heNonloop : M.IsNonloop e := Matroid.isNonloop_of_loopless he
  have hfNonloop : M.IsNonloop f := Matroid.isNonloop_of_loopless hf
  by_contra hdep
  apply hclosure
  exact (heNonloop.closure_eq_closure_iff_eq_or_dep hfNonloop).2 (Or.inr hdep)

/-- Every singleton-closure part inherits the uniform-density size bound. -/
theorem card_closureFinpartition_part_le
    (M : Matroid α) (k : ℕ)
    (hDense : UniformlyDense M k) (hLoopless : M.Loopless)
    [Fintype M.E] [DecidableEq M.E]
    (p : Finset M.E) (hp : p ∈ (closureFinpartition M).parts) :
    p.card ≤ k := by
  let P : Finpartition (Finset.univ : Finset M.E) := closureFinpartition M
  obtain ⟨e, he⟩ := P.nonempty_of_mem_parts (by simpa [P] using hp)
  have hpart : P.part e = p := P.part_eq_of_mem (by simpa [P] using hp) he
  have himage :
      (fun x : M.E => (x : α)) '' (↑p : Set M.E) ⊆
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
      (p.card : ℕ∞) = (↑p : Set M.E).encard := by simp
      _ = ((fun x : M.E => (x : α)) '' (↑p : Set M.E)).encard :=
        (Subtype.val_injective.encard_image (↑p : Set M.E)).symm
      _ ≤ (M.closure ({(e : α)} : Set α)).encard := Set.encard_mono himage
      _ ≤ (k : ℕ∞) :=
        closure_singleton_encard_le M k hDense hLoopless e.property
  exact_mod_cast hcardENat

/--
A finite uniformly dense rank-two matroid has a cyclic half-weave whose every
successor pair is a basis.
-/
theorem exists_cyclic_adjacent_base_order_of_uniformlyDense_direct
    (M : Matroid α) (k : ℕ)
    [Fintype M.E] [DecidableEq M.E]
    (hk : 0 < k)
    (hcard : Fintype.card M.E = 2 * k)
    (hDense : UniformlyDense M k)
    (hRank : M.eRank = 2) :
    ∃ order : Fin k × Bool ≃ M.E,
      ∀ p : Fin k × Bool,
        M.IsBase
          ({((order p : M.E) : α),
            ((order (weaveNext k hk p) : M.E) : α)} : Set α) := by
  have hLoopless : M.Loopless := loopless_of_uniformlyDense M k hk hDense
  have hbound : ∀ q : (closureFinpartition M).parts, q.1.card ≤ k := by
    intro q
    exact card_closureFinpartition_part_le M k hDense hLoopless q.1 q.2
  obtain ⟨y, S, hclassify⟩ :=
    FinitePartition.exists_largestFirst_enumeration
      (closureFinpartition M) k hk hcard hbound
  let order : Fin k × Bool ≃ M.E := woven k hk y
  refine ⟨order, ?_⟩
  intro p
  let a : Fin (2 * k) := halfWeaveEquiv k hk p
  let b : Fin (2 * k) := halfWeaveEquiv k hk (weaveNext k hk p)
  have hblocks : S.block a ≠ S.block b := by
    simpa [a, b] using largestFirst_woven_successor_blocks_ne hk S p
  have hclosure :
      M.closure ({((y a : M.E) : α)} : Set α) ≠
        M.closure ({((y b : M.E) : α)} : Set α) := by
    intro hcl
    apply hblocks
    apply (hclassify a b).2
    have hmem : y b ∈ (closureFinpartition M).part (y a) :=
      (mem_closureFinpartition_part_iff M (y a) (y b)).2 hcl
    have hpartMem :
        (closureFinpartition M).part (y a) ∈ (closureFinpartition M).parts :=
      (closureFinpartition M).part_mem.2 (Finset.mem_univ _)
    have hrev :
        (closureFinpartition M).part (y b) =
          (closureFinpartition M).part (y a) :=
      ((closureFinpartition M).part_eq_iff_mem hpartMem).2 hmem
    exact hrev.symm
  have hab : a ≠ b := by
    intro hab
    apply hblocks
    exact congrArg S.block hab
  have hyne : y a ≠ y b := by
    intro hy
    exact hab (y.injective hy)
  have hne : ((y a : M.E) : α) ≠ ((y b : M.E) : α) := by
    intro hcoe
    apply hyne
    exact Subtype.ext hcoe
  have hindep :
      M.Indep ({((y a : M.E) : α), ((y b : M.E) : α)} : Set α) :=
    pair_indep_of_closure_ne M hLoopless (y a).property (y b).property hclosure
  have hbase :
      M.IsBase ({((y a : M.E) : α), ((y b : M.E) : α)} : Set α) :=
    pair_isBase_of_indep_of_eRank_eq_two M hRank hne hindep
  simpa [order, woven, a, b] using hbase

end

end HigherRankKUM.RankTwo
