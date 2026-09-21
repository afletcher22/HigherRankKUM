import HigherRankKUM.LocalExchangeClosure
import HigherRankKUM.CyclicWindowCardinality
import HigherRankKUM.Rank4.FourBlockMove
import Mathlib.Tactic

namespace HigherRankKUM
namespace Rank4PositionSwapRigidity

open Set
open scoped Matroid

noncomputable section

variable {alpha : Type*}

/-- Swap two positions of a cyclic enumeration. -/
def swapPositions
    {E : Set alpha} {n : ℕ}
    (sigma : Fin n ≃ E) (p q : Fin n) :
    Fin n ≃ E :=
  (Equiv.swap p q).trans sigma

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
  · rintro ⟨r, rfl⟩
    let z := cyclicIndex n hn i r.val
    have hzP :
        z ∈ Rank4FourBlockMove.cyclicPositionWindow 4 hn i := ⟨r, rfl⟩
    by_cases hzp : z = p
    · subst z
      simp [swapPositions, Equiv.swap_apply_def, hp, hq]
    · have hzq : z ≠ q := by
        intro hzq
        subst z
        exact hq hzP
      have hswap : Equiv.swap p q z = z := by
        simp [Equiv.swap_apply_def, hzp, hzq]
      rw [swapPositions_apply, hswap]
      refine Or.inr ⟨⟨r, rfl⟩, ?_⟩
      intro hEq
      apply hzp
      apply sigma.injective
      apply Subtype.ext
      exact hEq
  · intro hx
    rcases hx with hqval | hx
    · rcases hp with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      change
        (sigma (Equiv.swap p q (cyclicIndex n hn i r.val)) : alpha) = x
      rw [← hr]
      simpa [Equiv.swap_apply_def] using hqval.symm
    · rcases hx with ⟨hxW, hxne⟩
      rcases hxW with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      let z := cyclicIndex n hn i r.val
      have hzP :
          z ∈ Rank4FourBlockMove.cyclicPositionWindow 4 hn i := ⟨r, rfl⟩
      have hzp : z ≠ p := by
        intro hzp
        subst z
        apply hxne
        simpa using hr.symm
      have hzq : z ≠ q := by
        intro hzq
        subst z
        exact hq hzP
      have hswap : Equiv.swap p q z = z := by
        simp [Equiv.swap_apply_def, hzp, hzq]
      change (sigma (Equiv.swap p q z) : alpha) = x
      rw [hswap]
      exact hr

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
