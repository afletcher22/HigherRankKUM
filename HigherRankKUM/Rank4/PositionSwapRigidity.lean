import HigherRankKUM.LocalExchangeClosure
import HigherRankKUM.CyclicWindowCardinality
import HigherRankKUM.Rank4.FourBlockMove
import HigherRankKUM.Rank4.FourBlockPerm
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4PositionSwapRigidity

open Set
open scoped Matroid

noncomputable section

variable {alpha : Type*}

/-- Extending a transposition of two local four-block coordinates is exactly
the global transposition of their two embedded cyclic positions. -/
theorem supportedFourBlockPerm_swap
    {n : ℕ} (hn : 0 < n) (h4n : 4 ≤ n)
    (s : Fin n) (a b : Fin 4) :
    Rank4FourBlockMove.supportedFourBlockPerm hn h4n s (Equiv.swap a b) =
      Equiv.swap
        (cyclicIndex n hn s a.val)
        (cyclicIndex n hn s b.val) := by
  apply Equiv.ext
  intro i
  by_cases hi : i ∈ Rank4FourBlockMove.fourBlockPositions hn s
  · rw [← Rank4FourBlockMove.range_fourBlockEmbedding_eq_fourBlockPositions
      hn h4n s] at hi
    rcases hi with ⟨q, rfl⟩
    rw [Rank4FourBlockMove.supportedFourBlockPerm_apply_block]
    change
      Rank4FourBlockMove.fourBlockEmbedding hn h4n s (Equiv.swap a b q) =
        Equiv.swap
          (Rank4FourBlockMove.fourBlockEmbedding hn h4n s a)
          (Rank4FourBlockMove.fourBlockEmbedding hn h4n s b)
          (Rank4FourBlockMove.fourBlockEmbedding hn h4n s q)
    by_cases hqa : q = a
    · subst q
      simp
    by_cases hqb : q = b
    · subst q
      simp
    · have hfa :
          Rank4FourBlockMove.fourBlockEmbedding hn h4n s q ≠
            Rank4FourBlockMove.fourBlockEmbedding hn h4n s a := by
        intro h
        exact hqa ((Rank4FourBlockMove.fourBlockEmbedding hn h4n s).injective h)
      have hfb :
          Rank4FourBlockMove.fourBlockEmbedding hn h4n s q ≠
            Rank4FourBlockMove.fourBlockEmbedding hn h4n s b := by
        intro h
        exact hqb ((Rank4FourBlockMove.fourBlockEmbedding hn h4n s).injective h)
      rw [Equiv.swap_apply_of_ne_of_ne hqa hqb,
        Equiv.swap_apply_of_ne_of_ne hfa hfb]
  · rw [Rank4FourBlockMove.supportedFourBlockPerm_apply_outside
      hn h4n s (Equiv.swap a b) hi]
    have hia :
        i ≠ cyclicIndex n hn s a.val := by
      intro h
      apply hi
      rw [← Rank4FourBlockMove.range_fourBlockEmbedding_eq_fourBlockPositions
        hn h4n s]
      exact ⟨a, by
        change Rank4FourBlockMove.fourBlockEmbedding hn h4n s a = i
        simpa using h.symm⟩
    have hib :
        i ≠ cyclicIndex n hn s b.val := by
      intro h
      apply hi
      rw [← Rank4FourBlockMove.range_fourBlockEmbedding_eq_fourBlockPositions
        hn h4n s]
      exact ⟨b, by
        change Rank4FourBlockMove.fourBlockEmbedding hn h4n s b = i
        simpa using h.symm⟩
    rw [Equiv.swap_apply_of_ne_of_ne hia hib]

/-- Swap two positions of a cyclic enumeration. -/
def swapPositions
    {E : Set alpha} {n : ℕ}
    (sigma : Fin n ≃ E) (p q : Fin n) :
    Fin n ≃ E :=
  (Equiv.swap p q).trans sigma

/-- A local transposition inside a four-block is literally the global
position swap of the corresponding two cyclic positions. -/
theorem applyFourBlockPerm_swap_eq_swapPositions
    {E : Set alpha} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (sigma : Fin n ≃ E) (s : Fin n)
    (a b : Fin 4) :
    Rank4FourBlockMove.applyFourBlockPerm hn h4n sigma s (Equiv.swap a b) =
      swapPositions sigma
        (cyclicIndex n hn s a.val)
        (cyclicIndex n hn s b.val) := by
  apply Equiv.ext
  intro i
  change
    sigma
        (Rank4FourBlockMove.supportedFourBlockPerm
          hn h4n s (Equiv.swap a b) i) =
      sigma
        (Equiv.swap
          (cyclicIndex n hn s a.val)
          (cyclicIndex n hn s b.val) i)
  rw [supportedFourBlockPerm_swap hn h4n s a b]

@[simp]
theorem swapPositions_apply
    {E : Set alpha} {n : ℕ}
    (sigma : Fin n ≃ E) (p q i : Fin n) :
    swapPositions sigma p q i =
      sigma (Equiv.swap p q i) := by
  rfl

/-- If a rank-four position window contains p but not q, swapping the two
positions replaces exactly sigma(p) by sigma(q) in that window. -/
theorem cyclicWindow_swapPositions_eq_insert_sdiff_of_mem_notMem
    {E : Set alpha} {n : ℕ}
    (hn : 0 < n) (sigma : Fin n ≃ E)
    (p q i : Fin n)
    (hp : p ∈ Rank4FourBlockMove.cyclicPositionWindow 4 hn i)
    (hq : q ∉ Rank4FourBlockMove.cyclicPositionWindow 4 hn i) :
    cyclicWindow 4 hn (swapPositions sigma p q) i =
      insert (sigma q : alpha)
        (cyclicWindow 4 hn sigma i \ {(sigma p : alpha)}) := by
  ext x
  constructor
  · rintro ⟨r, hr⟩
    let z := cyclicIndex n hn i r.val
    have hzP :
        z ∈ Rank4FourBlockMove.cyclicPositionWindow 4 hn i := ⟨r, rfl⟩
    have hx :
        x = (sigma (Equiv.swap p q z) : alpha) := by
      simpa [swapPositions, z] using hr.symm
    by_cases hzp : z = p
    · subst z
      left
      simpa using hx
    · have hzq : z ≠ q := by
        intro hzq
        subst z
        exact hq hzP
      right
      have hswap : Equiv.swap p q z = z :=
        Equiv.swap_apply_of_ne_of_ne hzp hzq
      have hxz : x = (sigma z : alpha) := by
        simpa [hswap] using hx
      constructor
      · refine ⟨r, ?_⟩
        exact hxz
      · intro hxp
        apply hzp
        apply sigma.injective
        apply Subtype.ext
        exact hxz.symm.trans hxp
  · intro hx
    rcases hx with hxq | ⟨hxW, hxp⟩
    · rcases hp with ⟨r, hrp⟩
      refine ⟨r, ?_⟩
      have hpidx :
          cyclicIndex n hn i r.val = p := hrp
      subst p
      simpa [swapPositions] using hxq.symm
    · rcases hxW with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      let z := cyclicIndex n hn i r.val
      have hzP :
          z ∈ Rank4FourBlockMove.cyclicPositionWindow 4 hn i := ⟨r, rfl⟩
      have hzp : z ≠ p := by
        intro h
        subst z
        apply hxp
        exact hr
      have hzq : z ≠ q := by
        intro h
        subst z
        exact hq hzP
      have hswap : Equiv.swap p q z = z :=
        Equiv.swap_apply_of_ne_of_ne hzp hzq
      simpa [swapPositions, z, hswap] using hr

/-- If a position window contains either both swapped positions or neither,
swapping those positions leaves the window unchanged as a set of ground
elements. -/
theorem cyclicWindow_swapPositions_eq_of_mem_iff
    {E : Set alpha} {n : ℕ}
    (hn : 0 < n) (sigma : Fin n ≃ E)
    (p q i : Fin n)
    (hiff :
      p ∈ Rank4FourBlockMove.cyclicPositionWindow 4 hn i ↔
      q ∈ Rank4FourBlockMove.cyclicPositionWindow 4 hn i) :
    cyclicWindow 4 hn (swapPositions sigma p q) i =
      cyclicWindow 4 hn sigma i := by
  let P := Rank4FourBlockMove.cyclicPositionWindow 4 hn i
  have hpres :
      ∀ {z : Fin n}, z ∈ P → Equiv.swap p q z ∈ P := by
    intro z hz
    by_cases hzp : z = p
    · subst z
      simpa [P] using hiff.mp (by simpa [P] using hz)
    by_cases hzq : z = q
    · subst z
      simpa [P] using hiff.mpr (by simpa [P] using hz)
    · rw [Equiv.swap_apply_of_ne_of_ne hzp hzq]
      exact hz
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    let z := cyclicIndex n hn i r.val
    have hzP : z ∈ P := by
      exact ⟨r, rfl⟩
    have hswP := hpres hzP
    rcases hswP with ⟨r', hr'⟩
    refine ⟨r', ?_⟩
    change
      (sigma (Equiv.swap p q z) : alpha) =
        (sigma (cyclicIndex n hn i r'.val) : alpha)
    rw [hr']
  · rintro ⟨r, rfl⟩
    let z := cyclicIndex n hn i r.val
    have hzP : z ∈ P := by
      exact ⟨r, rfl⟩
    have hswP := hpres hzP
    rcases hswP with ⟨r', hr'⟩
    refine ⟨r', ?_⟩
    change
      (sigma (Equiv.swap p q (cyclicIndex n hn i r'.val)) : alpha) =
        (sigma z : alpha)
    rw [hr']
    simp

/-- A dependent window produced by a one-sided position swap gives a closure
obstruction on the unchanged three-element core. -/
theorem mem_closure_of_dep_swap_window
    {M : Matroid alpha} {E : Set alpha} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (sigma : Fin n ≃ E)
    (p q i : Fin n)
    (hCBO : CyclicBasisOrder M 4 hn sigma)
    (hp : p ∈ Rank4FourBlockMove.cyclicPositionWindow 4 hn i)
    (hq : q ∉ Rank4FourBlockMove.cyclicPositionWindow 4 hn i)
    (hdep : M.Dep (cyclicWindow 4 hn (swapPositions sigma p q) i)) :
    (sigma q : alpha) ∈
      M.closure
        (cyclicWindow 4 hn sigma i \ {(sigma p : alpha)}) := by
  let C := cyclicWindow 4 hn sigma i \ {(sigma p : alpha)}
  have hCoreInd : M.Indep C := by
    exact (hCBO i).indep.subset Set.sdiff_subset
  have hdep' : M.Dep (insert (sigma q : alpha) C) := by
    rw [← cyclicWindow_swapPositions_eq_insert_sdiff_of_mem_notMem
      hn sigma p q i hp hq]
    exact hdep
  by_cases hqC : (sigma q : alpha) ∈ C
  · exact M.subset_closure C hCoreInd.subset_ground hqC
  · exact (hCoreInd.mem_closure_iff_of_notMem hqC).2 hdep'


/-- Global failed-swap rigidity.

If swapping two cyclic positions destroys a rank-four cyclic basis ordering,
then some basis window contains exactly one of the swapped positions.  In that
window the incoming element is spanned by the unchanged three-element core.

This packages all transposition-type local moves (adjacent, endpoint, and
side swaps) into one representation-free obstruction theorem. -/
theorem exists_closure_obstruction_of_not_cyclicBasisOrder_swapPositions
    {M : Matroid alpha} {E : Set alpha} {n : ℕ}
    (hn : 0 < n) (h4n : 4 ≤ n)
    (hEsub : E ⊆ M.E)
    (hRank : M.eRank = (4 : ℕ∞))
    (sigma : Fin n ≃ E) (p q : Fin n)
    (hCBO : CyclicBasisOrder M 4 hn sigma)
    (hfail :
      ¬ CyclicBasisOrder M 4 hn (swapPositions sigma p q)) :
    ∃ i : Fin n,
      (p ∈ Rank4FourBlockMove.cyclicPositionWindow 4 hn i ∧
       q ∉ Rank4FourBlockMove.cyclicPositionWindow 4 hn i ∧
       (sigma q : alpha) ∈
         M.closure
           (cyclicWindow 4 hn sigma i \ {(sigma p : alpha)})) ∨
      (q ∈ Rank4FourBlockMove.cyclicPositionWindow 4 hn i ∧
       p ∉ Rank4FourBlockMove.cyclicPositionWindow 4 hn i ∧
       (sigma p : alpha) ∈
         M.closure
           (cyclicWindow 4 hn sigma i \ {(sigma q : alpha)})) := by
  have hex :
      ∃ i : Fin n,
        ¬ M.IsBase (cyclicWindow 4 hn (swapPositions sigma p q) i) := by
    simpa [CyclicBasisOrder] using hfail
  rcases hex with ⟨i, hnot⟩
  let P := Rank4FourBlockMove.cyclicPositionWindow 4 hn i
  by_cases hp : p ∈ P
  · by_cases hq : q ∈ P
    · exfalso
      apply hnot
      rw [cyclicWindow_swapPositions_eq_of_mem_iff
        hn sigma p q i (by
          constructor <;> intro _ <;> assumption)]
      exact hCBO i
    · have hdep :
          M.Dep (cyclicWindow 4 hn (swapPositions sigma p q) i) :=
        cyclicWindow_four_dep_of_not_isBase
          hn h4n hEsub hRank (swapPositions sigma p q) i hnot
      refine ⟨i, Or.inl ⟨hp, hq, ?_⟩⟩
      exact mem_closure_of_dep_swap_window
        hn h4n sigma p q i hCBO hp hq hdep
  · by_cases hq : q ∈ P
    · have hdep :
          M.Dep (cyclicWindow 4 hn (swapPositions sigma p q) i) :=
        cyclicWindow_four_dep_of_not_isBase
          hn h4n hEsub hRank (swapPositions sigma p q) i hnot
      have hdep' :
          M.Dep (cyclicWindow 4 hn (swapPositions sigma q p) i) := by
        simpa [swapPositions, Equiv.swap_comm] using hdep
      refine ⟨i, Or.inr ⟨hq, hp, ?_⟩⟩
      exact mem_closure_of_dep_swap_window
        hn h4n sigma q p i hCBO hq hp hdep'
    · exfalso
      apply hnot
      rw [cyclicWindow_swapPositions_eq_of_mem_iff
        hn sigma p q i (by
          constructor
          · intro hp'
            exact (hp hp').elim
          · intro hq'
            exact (hq hq').elim)]
      exact hCBO i

end

end Rank4PositionSwapRigidity
end HigherRankKUM
