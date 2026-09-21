import HigherRankKUM.StrictDensity
import HigherRankKUM.Rank4.T0FixedELocalGeometry

namespace HigherRankKUM
namespace Rank4FixedEThreeRunCap

open Set
open scoped Matroid

noncomputable section

variable {α : Type*}

/-- Starts of length-three blocker runs for a fixed omitted element. -/
def threeBlockerRunStarts
    (M : Matroid α) {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) (e : α) :
    Set (Fin n) :=
  {i |
    Rank4BlockerCycle.blockerAt M hn σ e i ∧
    Rank4BlockerCycle.blockerAt M hn σ e (cyclicIndex n hn i 1) ∧
    Rank4BlockerCycle.blockerAt M hn σ e (cyclicIndex n hn i 2)}

/-- Strict density in a rank-four `4k+2` instance bounds the full parallel
class of a nonloop by `k` elements. -/
theorem parallel_class_ncard_le_k
    {M : Matroid α} {k : ℕ} {e : α}
    (hGroundFin : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (he : M.IsNonloop e) :
    (M.closure ({e} : Set α)).ncard ≤ k := by
  have hclSub : M.closure ({e} : Set α) ⊆ M.E :=
    M.closure_subset_ground _
  have hclFin : (M.closure ({e} : Set α)).Finite :=
    hGroundFin.subset hclSub
  have hclNonempty : (M.closure ({e} : Set α)).Nonempty := by
    refine ⟨e, ?_⟩
    exact M.subset_closure ({e} : Set α) (by simpa using he.mem_ground) (by simp)
  have hclRank : M.eRk (M.closure ({e} : Set α)) = (1 : ℕ∞) := by
    rw [M.eRk_closure_eq, he.eRk_eq]
  have hclProper : M.closure ({e} : Set α) ≠ M.E := by
    intro hEq
    have hr := hclRank
    rw [hEq, M.eRk_ground, hRank] at hr
    norm_num at hr
  have hs :=
    hStrict (M.closure ({e} : Set α))
      hclSub hclNonempty hclProper
  rw [← hclFin.cast_ncard_eq, hclRank] at hs
  have hsNat :
      4 * (M.closure ({e} : Set α)).ncard < (4 * k + 2) * 1 := by
    exact_mod_cast hs
  omega

/-- The center map of three-blocker runs is injective: shifting every cyclic
start by two positions and then reading the cyclic order preserves
distinctness. -/
theorem threeRunCenter_injective
    {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) :
    Function.Injective
      (fun i : Fin n => (σ (cyclicIndex n hn i 2) : α)) := by
  intro i j hij
  apply cyclicIndex_injective_start n hn 2
  apply σ.injective
  apply Subtype.ext
  exact hij

/-- In a deletion CBO, the center element of every three-blocker run lies in
the parallel class of the omitted nonloop `e`. -/
theorem threeRunCenter_mem_parallel_class
    {M : Matroid α} {E : Set α} {n : ℕ}
    (hn : 0 < n) (h5n : 5 ≤ n)
    (hEsub : E ⊆ M.E)
    (σ : Fin n ≃ E) (e : α)
    (he : M.IsNonloop e)
    (heE : e ∉ E)
    (hCBO : CyclicBasisOrder M 4 hn σ)
    {i : Fin n}
    (hi : i ∈ threeBlockerRunStarts M hn σ e) :
    (σ (cyclicIndex n hn i 2) : α) ∈ M.closure ({e} : Set α) := by
  rcases hi with ⟨h0, h1, h2⟩
  let x : α := (σ (cyclicIndex n hn i 2) : α)
  have hspan : e ∈ M.closure ({x} : Set α) := by
    dsimp [x]
    exact Rank4BlockerRuns.three_consecutive_blockers_mem_closure_shared_singleton
      hn h5n σ e hCBO i h0 h1 h2
  have hclEq : M.closure ({e} : Set α) = M.closure ({x} : Set α) :=
    he.closure_eq_of_mem_closure hspan
  have hxGround : x ∈ M.E :=
    hEsub (σ (cyclicIndex n hn i 2)).property
  have hxSelf : x ∈ M.closure ({x} : Set α) :=
    M.subset_closure ({x} : Set α) (by simpa using hxGround) (by simp)
  rw [hclEq]
  exact hxSelf

/-- Distinct three-blocker runs have distinct parallel mates, and the omitted
element itself is not among those mates. Hence strict density gives at most
`k-1` three-blocker runs around a `4k+1` deletion cycle. -/
theorem threeBlockerRunStarts_ncard_le_k_sub_one
    {M : Matroid α} {E : Set α} {k : ℕ}
    (hk : 1 ≤ k)
    (hGroundFin : M.E.Finite)
    (hRank : M.eRank = (4 : ℕ∞))
    (hStrict : StrictlyUniformlyDenseRatio M (4 * k + 2) 4)
    (hEsub : E ⊆ M.E)
    (σ : Fin (4 * k + 1) ≃ E) (e : α)
    (he : M.IsNonloop e)
    (heE : e ∉ E)
    (hCBO : CyclicBasisOrder M 4 (by omega) σ) :
    (threeBlockerRunStarts M (by omega) σ e).ncard ≤ k - 1 := by
  let R := threeBlockerRunStarts M (by omega) σ e
  let f : Fin (4 * k + 1) → α :=
    fun i => (σ (cyclicIndex (4 * k + 1) (by omega) i 2) : α)
  have hfInj : Function.Injective f := by
    dsimp [f]
    exact threeRunCenter_injective (by omega) σ
  have himgSub : f '' R ⊆ M.closure ({e} : Set α) := by
    intro x hx
    rcases hx with ⟨i, hiR, rfl⟩
    dsimp [f]
    exact threeRunCenter_mem_parallel_class
      (M := M) (hn := by omega) (h5n := by omega)
      hEsub σ e he heE hCBO hiR
  have heCl : e ∈ M.closure ({e} : Set α) := by
    exact (M.subset_closure ({e} : Set α) (by simpa using he.mem_ground)) (by simp)
  have heNotImg : e ∉ f '' R := by
    rintro ⟨i, -, hi⟩
    apply heE
    have hiE : f i ∈ E := (σ (cyclicIndex (4 * k + 1) (by omega) i 2)).property
    rw [← hi]
    exact hiE
  have himgNe : f '' R ≠ M.closure ({e} : Set α) := by
    intro hEq
    apply heNotImg
    rw [hEq]
    exact heCl
  have hclFin : (M.closure ({e} : Set α)).Finite :=
    hGroundFin.subset (M.closure_subset_ground _)
  have hlt :
      (f '' R).ncard < (M.closure ({e} : Set α)).ncard :=
    Set.ncard_lt_ncard (himgSub.ssubset_of_ne himgNe) hclFin
  have hRcard : (f '' R).ncard = R.ncard :=
    Set.ncard_image_of_injective R hfInj
  have hcap :=
    parallel_class_ncard_le_k hGroundFin hRank hStrict he
  rw [hRcard] at hlt
  dsimp [R] at hlt ⊢
  omega

end

end Rank4FixedEThreeRunCap
end HigherRankKUM
