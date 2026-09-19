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


/-- Two loopless rank-two matroids on the same ground set have a common
independent two-element set. This is the rank-two "common pair" lemma used by
the direct rank-four dangerous-core construction. -/
theorem exists_common_indep_pair
    (M N : Matroid α)
    (hground : M.E = N.E)
    (hMloopless : M.Loopless)
    (hNloopless : N.Loopless)
    (hMrank : M.eRank = 2)
    (hNrank : N.eRank = 2) :
    ∃ e f : α, e ≠ f ∧ e ∈ M.E ∧ f ∈ M.E ∧
      M.Indep ({e, f} : Set α) ∧ N.Indep ({e, f} : Set α) := by
  obtain ⟨BM, hBM⟩ := M.exists_isBase
  have hBMcard : BM.encard = 2 := by
    simpa [hMrank] using hBM.encard_eq_eRank
  obtain ⟨a, b, hab, hBMpair⟩ := Set.encard_eq_two.mp hBMcard
  have haM : a ∈ M.E := hBM.subset_ground (by rw [hBMpair]; simp)
  have hbM : b ∈ M.E := hBM.subset_ground (by rw [hBMpair]; simp)
  have hMab : M.Indep ({a, b} : Set α) := by
    rw [← hBMpair]
    exact hBM.indep
  have haN : a ∈ N.E := by
    rw [← hground]
    exact haM
  have hbN : b ∈ N.E := by
    rw [← hground]
    exact hbM
  by_cases hNab : N.Indep ({a, b} : Set α)
  · exact ⟨a, b, hab, haM, hbM, hMab, hNab⟩
  have haMnonloop : M.IsNonloop a := by
    let : M.Loopless := hMloopless
    exact Matroid.isNonloop_of_loopless haM
  have hbMnonloop : M.IsNonloop b := by
    let : M.Loopless := hMloopless
    exact Matroid.isNonloop_of_loopless hbM
  have haNnonloop : N.IsNonloop a := by
    let : N.Loopless := hNloopless
    exact Matroid.isNonloop_of_loopless haN
  have hbNnonloop : N.IsNonloop b := by
    let : N.Loopless := hNloopless
    exact Matroid.isNonloop_of_loopless hbN
  have hMclab :
      M.closure ({a} : Set α) ≠ M.closure ({b} : Set α) := by
    intro hcl
    rcases (haMnonloop.closure_eq_closure_iff_eq_or_dep hbMnonloop).1 hcl with
      hab' | hdep
    · exact hab hab'
    · exact hdep hMab
  have hNclab :
      N.closure ({a} : Set α) = N.closure ({b} : Set α) :=
    (haNnonloop.closure_eq_closure_iff_eq_or_dep hbNnonloop).2 (Or.inr hNab)

  obtain ⟨BN, hBN⟩ := N.exists_isBase
  have hBNcard : BN.encard = 2 := by
    simpa [hNrank] using hBN.encard_eq_eRank
  obtain ⟨c, d, hcd, hBNpair⟩ := Set.encard_eq_two.mp hBNcard
  have hcN : c ∈ N.E := hBN.subset_ground (by rw [hBNpair]; simp)
  have hdN : d ∈ N.E := hBN.subset_ground (by rw [hBNpair]; simp)
  have hNcd : N.Indep ({c, d} : Set α) := by
    rw [← hBNpair]
    exact hBN.indep
  have hcM : c ∈ M.E := by
    rw [hground]
    exact hcN
  have hdM : d ∈ M.E := by
    rw [hground]
    exact hdN
  have hcNnonloop : N.IsNonloop c := by
    let : N.Loopless := hNloopless
    exact Matroid.isNonloop_of_loopless hcN
  have hdNnonloop : N.IsNonloop d := by
    let : N.Loopless := hNloopless
    exact Matroid.isNonloop_of_loopless hdN
  have hNclcd :
      N.closure ({c} : Set α) ≠ N.closure ({d} : Set α) := by
    intro hcl
    rcases (hcNnonloop.closure_eq_closure_iff_eq_or_dep hdNnonloop).1 hcl with
      hcd' | hdep
    · exact hcd hcd'
    · exact hdep hNcd

  by_cases hac :
      N.closure ({a} : Set α) = N.closure ({c} : Set α)
  · have had :
        N.closure ({a} : Set α) ≠ N.closure ({d} : Set α) := by
      intro had'
      exact hNclcd (hac.symm.trans had')
    have hNad : N.Indep ({a, d} : Set α) :=
      pair_indep_of_closure_ne N hNloopless haN hdN had
    have hadne : a ≠ d := by
      intro h
      subst d
      exact had rfl
    by_cases hMad : M.Indep ({a, d} : Set α)
    · exact ⟨a, d, hadne, haM, hdM, hMad, hNad⟩
    · have hdMnonloop : M.IsNonloop d := by
        let : M.Loopless := hMloopless
        exact Matroid.isNonloop_of_loopless hdM
      have hMclad :
          M.closure ({a} : Set α) = M.closure ({d} : Set α) :=
        (haMnonloop.closure_eq_closure_iff_eq_or_dep hdMnonloop).2 (Or.inr hMad)
      have hMclbd :
          M.closure ({b} : Set α) ≠ M.closure ({d} : Set α) := by
        intro hbd
        exact hMclab (hMclad.trans hbd.symm)
      have hNclbd :
          N.closure ({b} : Set α) ≠ N.closure ({d} : Set α) := by
        intro hbd
        exact had (hNclab.trans hbd)
      have hMbd : M.Indep ({b, d} : Set α) :=
        pair_indep_of_closure_ne M hMloopless hbM hdM hMclbd
      have hNbd : N.Indep ({b, d} : Set α) :=
        pair_indep_of_closure_ne N hNloopless hbN hdN hNclbd
      have hbdne : b ≠ d := by
        intro h
        subst d
        exact hNclbd rfl
      exact ⟨b, d, hbdne, hbM, hdM, hMbd, hNbd⟩
  · have hNac : N.Indep ({a, c} : Set α) :=
      pair_indep_of_closure_ne N hNloopless haN hcN hac
    have hacne : a ≠ c := by
      intro h
      subst c
      exact hac rfl
    by_cases hMac : M.Indep ({a, c} : Set α)
    · exact ⟨a, c, hacne, haM, hcM, hMac, hNac⟩
    · have hcMnonloop : M.IsNonloop c := by
        let : M.Loopless := hMloopless
        exact Matroid.isNonloop_of_loopless hcM
      have hMclac :
          M.closure ({a} : Set α) = M.closure ({c} : Set α) :=
        (haMnonloop.closure_eq_closure_iff_eq_or_dep hcMnonloop).2 (Or.inr hMac)
      have hMclbc :
          M.closure ({b} : Set α) ≠ M.closure ({c} : Set α) := by
        intro hbc
        exact hMclab (hMclac.trans hbc.symm)
      have hNclbc :
          N.closure ({b} : Set α) ≠ N.closure ({c} : Set α) := by
        intro hbc
        exact hac (hNclab.trans hbc)
      have hMbc : M.Indep ({b, c} : Set α) :=
        pair_indep_of_closure_ne M hMloopless hbM hcM hMclbc
      have hNbc : N.Indep ({b, c} : Set α) :=
        pair_indep_of_closure_ne N hNloopless hbN hcN hNclbc
      have hbcne : b ≠ c := by
        intro h
        subst c
        exact hNclbc rfl
      exact ⟨b, c, hbcne, hbM, hcM, hMbc, hNbc⟩

end

end HigherRankKUM.RankTwo
