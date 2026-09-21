import Rank3KUM.CyclicOrder
import Rank3KUM.FinalReduction
import Rank3KUM.StrictDensity
import Rank3KUM.SixPointCombinatorics

namespace Rank3KUM

open Set

variable {α : Type*}

/--
Strict density at parameter two makes every pair of distinct ground elements
independent.
-/
theorem pair_indep_of_strict_two
    (M : Matroid α)
    (hLoopless : M.Loopless)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hStrict : StrictlyUniformlyDense M 2)
    {a b : α}
    (haE : a ∈ M.E)
    (hbE : b ∈ M.E)
    (hab : a ≠ b) :
    M.Indep ({a, b} : Set α) := by
  let : M.Loopless := hLoopless
  have haIndep : M.Indep ({a} : Set α) :=
    (Matroid.isNonloop_of_loopless haE).indep
  have hbNotMem : b ∉ ({a} : Set α) := by
    simpa using hab.symm
  by_contra hPairNotIndep
  have hbClosure : b ∈ M.closure ({a} : Set α) := by
    by_contra hbNotClosure
    have hInsertIndep :
        M.Indep (insert b ({a} : Set α)) :=
      (haIndep.notMem_closure_iff_of_notMem
        hbNotMem hbE).1 hbNotClosure
    apply hPairNotIndep
    simpa [pair_comm] using hInsertIndep
  have hClosureRank :
      M.eRk (M.closure ({a} : Set α)) = 1 := by
    rw [M.eRk_closure_eq, haIndep.eRk_eq_encard]
    simp
  have hClosureFinite :
      (M.closure ({a} : Set α)).Finite :=
    hE.subset (M.closure_subset_ground _)
  have hClosureNonempty :
      (M.closure ({a} : Set α)).Nonempty :=
    ⟨a, M.mem_closure_self _ haE⟩
  have hClosureProper :
      M.closure ({a} : Set α) ≠ M.E := by
    intro hEq
    have hGroundRank :
        M.eRk (M.closure ({a} : Set α)) = M.eRank := by
      rw [hEq, M.eRk_ground]
    rw [hClosureRank, hRank] at hGroundRank
    norm_num at hGroundRank
  have hClosureLt :=
    StrictlyUniformlyDense.encard_lt_k_of_eRk_eq_one
      M 2 hStrict (M.closure_subset_ground _)
      hClosureNonempty hClosureProper hClosureRank
  have hClosureNcardLt :
      (M.closure ({a} : Set α)).ncard < 2 := by
    rw [← hClosureFinite.cast_ncard_eq] at hClosureLt
    exact_mod_cast hClosureLt
  have hPairSubset :
      ({a, b} : Set α) ⊆ M.closure ({a} : Set α) := by
    intro x hx
    simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact M.mem_closure_self _ haE
    · exact hbClosure
  have hPairCardLe :
      ({a, b} : Set α).ncard ≤
        (M.closure ({a} : Set α)).ncard :=
    Set.ncard_le_ncard hPairSubset hClosureFinite
  have hPairCard : ({a, b} : Set α).ncard = 2 := by
    rw [Set.ncard_pair hab]
  omega

/--
In the strict `k = 2` case, two nonbasis triples cannot share a pair.
-/
theorem false_of_two_nonbase_triples_sharing_pair_strict_two
    (M : Matroid α)
    (hLoopless : M.Loopless)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hStrict : StrictlyUniformlyDense M 2)
    {a b c d : α}
    (haE : a ∈ M.E)
    (hbE : b ∈ M.E)
    (hcE : c ∈ M.E)
    (hdE : d ∈ M.E)
    (hab : a ≠ b)
    (hac : a ≠ c)
    (had : a ≠ d)
    (hbc : b ≠ c)
    (hbd : b ≠ d)
    (hcd : c ≠ d)
    (hABC :
      ¬ M.IsBase (insert c ({a, b} : Set α)))
    (hABD :
      ¬ M.IsBase (insert d ({a, b} : Set α))) :
    False := by
  let : M.Loopless := hLoopless
  have hPairIndep : M.Indep ({a, b} : Set α) :=
    pair_indep_of_strict_two
      M hLoopless hE hRank hStrict haE hbE hab
  have hcNotPair : c ∉ ({a, b} : Set α) := by
    simp [hac.symm, hbc.symm]
  have hdNotPair : d ∉ ({a, b} : Set α) := by
    simp [had.symm, hbd.symm]
  have hcClosure :
      c ∈ M.closure ({a, b} : Set α) := by
    by_contra hcNotClosure
    have hTripleIndep :
        M.Indep (insert c ({a, b} : Set α)) :=
      (hPairIndep.notMem_closure_iff_of_notMem
        hcNotPair hcE).1 hcNotClosure
    have hTripleCard :
        (insert c ({a, b} : Set α)).encard = 3 := by
      rw [Set.encard_insert_of_notMem hcNotPair,
        Set.encard_pair hab]
      norm_num
    apply hABC
    apply hTripleIndep.isBase_of_eRk_ge (by simp)
    exact le_of_eq
      (hRank.trans
        (hTripleCard.symm.trans
          hTripleIndep.eRk_eq_encard.symm))
  have hdClosure :
      d ∈ M.closure ({a, b} : Set α) := by
    by_contra hdNotClosure
    have hTripleIndep :
        M.Indep (insert d ({a, b} : Set α)) :=
      (hPairIndep.notMem_closure_iff_of_notMem
        hdNotPair hdE).1 hdNotClosure
    have hTripleCard :
        (insert d ({a, b} : Set α)).encard = 3 := by
      rw [Set.encard_insert_of_notMem hdNotPair,
        Set.encard_pair hab]
      norm_num
    apply hABD
    apply hTripleIndep.isBase_of_eRk_ge (by simp)
    exact le_of_eq
      (hRank.trans
        (hTripleCard.symm.trans
          hTripleIndep.eRk_eq_encard.symm))
  let U : Set α :=
    insert c (insert d ({a, b} : Set α))
  have hPairClosure :
      ({a, b} : Set α) ⊆ M.closure ({a, b} : Set α) :=
    M.subset_closure _
      (by simp [Set.insert_subset_iff,
        Set.singleton_subset_iff, haE, hbE])
  have hUSubsetClosure :
      U ⊆ M.closure ({a, b} : Set α) := by
    intro x hx
    change x ∈ insert c (insert d ({a, b} : Set α)) at hx
    simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hcClosure
    · exact hdClosure
    · exact hPairClosure (by simp)
    · exact hPairClosure (by simp)
  have hURankLe : M.eRk U ≤ 2 := by
    calc
      M.eRk U ≤ M.eRk (M.closure ({a, b} : Set α)) :=
        M.eRk_mono hUSubsetClosure
      _ = M.eRk ({a, b} : Set α) :=
        M.eRk_closure_eq _
      _ = ({a, b} : Set α).encard :=
        hPairIndep.eRk_eq_encard
      _ = 2 := Set.encard_pair hab
  have hUE : U ⊆ M.E := by
    intro x hx
    change x ∈ insert c (insert d ({a, b} : Set α)) at hx
    simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hcE
    · exact hdE
    · exact haE
    · exact hbE
  have hUNonempty : U.Nonempty := by
    exact ⟨c, by simp [U]⟩
  have hUProper : U ≠ M.E := by
    intro hEq
    have hGroundRank : M.eRk U = M.eRank := by
      rw [hEq, M.eRk_ground]
    have hThreeLeTwo : (3 : ℕ∞) ≤ 2 := by
      rw [← hRank, ← hGroundRank]
      exact hURankLe
    norm_num at hThreeLeTwo
  have hUCard : U.encard = 4 := by
    dsimp [U]
    rw [Set.encard_insert_of_notMem,
      Set.encard_insert_of_notMem hdNotPair,
      Set.encard_pair hab]
    · norm_num
    · simp [hac.symm, hbc.symm, hcd]
  have hLt := hStrict U hUE hUNonempty hUProper
  have hLtFour : U.encard < (4 : ℕ∞) := by
    refine hLt.trans_le ?_
    calc
      (2 : ℕ∞) * M.eRk U ≤ (2 : ℕ∞) * 2 := by
        gcongr
      _ = 4 := by norm_num
  rw [hUCard] at hLtFour
  exact (lt_irrefl (4 : ℕ∞)) hLtFour

/-- The ground-set image of a finite set of positions in a six-point enumeration. -/
def finSixSet
    (M : Matroid α)
    (order : Fin 6 ≃ M.E)
    (A : Finset (Fin 6)) : Set α :=
  (fun i : Fin 6 => (order i : α)) ''
    (A : Set (Fin 6))

/-- A position triple is bad when its ground-set image is not a basis. -/
def SixPointBad
    (M : Matroid α)
    (order : Fin 6 ≃ M.E)
    (A : Finset (Fin 6)) : Prop :=
  ¬ M.IsBase (finSixSet M order A)

/--
Two literal position triples with a common pair and distinct remaining
vertices cannot both be bad in the strict `k = 2` case.
-/
theorem not_both_sixPointBad_of_shared_pair
    (M : Matroid α)
    (hLoopless : M.Loopless)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hStrict : StrictlyUniformlyDense M 2)
    (order : Fin 6 ≃ M.E)
    {i j c d : Fin 6}
    (hij : i ≠ j)
    (hic : i ≠ c)
    (hid : i ≠ d)
    (hjc : j ≠ c)
    (hjd : j ≠ d)
    (hcd : c ≠ d) :
    ¬ (SixPointBad M order {i, j, c} ∧
      SixPointBad M order {i, j, d}) := by
  have hval :
      ∀ {u v : Fin 6}, u ≠ v →
        (order u : α) ≠ (order v : α) := by
    intro u v huv hEq
    apply huv
    apply order.injective
    exact Subtype.ext hEq
  rintro ⟨hBadC, hBadD⟩
  apply
    false_of_two_nonbase_triples_sharing_pair_strict_two
      M hLoopless hE hRank hStrict
      (order i).property (order j).property
      (order c).property (order d).property
      (hval hij) (hval hic) (hval hid)
      (hval hjc) (hval hjd) (hval hcd)
  · have h :
        ¬ M.IsBase
          ({(order i : α), (order j : α), (order c : α)} :
            Set α) := by
      simpa [SixPointBad, finSixSet,
        Set.image_insert_eq, Set.image_singleton] using hBadC
    have hset :
        ({(order c : α), (order i : α), (order j : α)} :
            Set α)
          = {(order i : α), (order j : α), (order c : α)} := by
      ext w
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact h
  · have h :
        ¬ M.IsBase
          ({(order i : α), (order j : α), (order d : α)} :
            Set α) := by
      simpa [SixPointBad, finSixSet,
        Set.image_insert_eq, Set.image_singleton] using hBadD
    have hset :
        ({(order d : α), (order i : α), (order j : α)} :
            Set α)
          = {(order i : α), (order j : α), (order d : α)} := by
      ext w
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact h

/-- Strict density at two makes the six-position bad-triple certificate linear. -/
theorem linearSixBad_of_strict_two
    (M : Matroid α)
    (hLoopless : M.Loopless)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hStrict : StrictlyUniformlyDense M 2)
    (order : Fin 6 ≃ M.E) :
    LinearSixBad (SixPointBad M order) := by
  unfold LinearSixBad
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (1 : Fin 6))
        (c := (2 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (1 : Fin 6))
        (c := (2 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (1 : Fin 6))
        (c := (2 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (2 : Fin 6))
        (c := (1 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 2, 1} : Finset (Fin 6)) = {0, 1, 2} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (2 : Fin 6))
        (c := (1 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 2, 1} : Finset (Fin 6)) = {0, 1, 2} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (2 : Fin 6))
        (c := (1 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 2, 1} : Finset (Fin 6)) = {0, 1, 2} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (2 : Fin 6))
        (c := (0 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 2, 0} : Finset (Fin 6)) = {0, 1, 2} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (2 : Fin 6))
        (c := (0 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 2, 0} : Finset (Fin 6)) = {0, 1, 2} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (2 : Fin 6))
        (c := (0 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 2, 0} : Finset (Fin 6)) = {0, 1, 2} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (1 : Fin 6))
        (c := (3 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (1 : Fin 6))
        (c := (3 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (3 : Fin 6))
        (c := (1 : Fin 6)) (d := (2 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 3, 1} : Finset (Fin 6)) = {0, 1, 3} from by decide] at h
    rw [show ({0, 3, 2} : Finset (Fin 6)) = {0, 2, 3} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (3 : Fin 6))
        (c := (1 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 3, 1} : Finset (Fin 6)) = {0, 1, 3} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (3 : Fin 6))
        (c := (1 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 3, 1} : Finset (Fin 6)) = {0, 1, 3} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (3 : Fin 6))
        (c := (0 : Fin 6)) (d := (2 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 3, 0} : Finset (Fin 6)) = {0, 1, 3} from by decide] at h
    rw [show ({1, 3, 2} : Finset (Fin 6)) = {1, 2, 3} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (3 : Fin 6))
        (c := (0 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 3, 0} : Finset (Fin 6)) = {0, 1, 3} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (3 : Fin 6))
        (c := (0 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 3, 0} : Finset (Fin 6)) = {0, 1, 3} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (1 : Fin 6))
        (c := (4 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (4 : Fin 6))
        (c := (1 : Fin 6)) (d := (2 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 4, 1} : Finset (Fin 6)) = {0, 1, 4} from by decide] at h
    rw [show ({0, 4, 2} : Finset (Fin 6)) = {0, 2, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (4 : Fin 6))
        (c := (1 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 4, 1} : Finset (Fin 6)) = {0, 1, 4} from by decide] at h
    rw [show ({0, 4, 3} : Finset (Fin 6)) = {0, 3, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (4 : Fin 6))
        (c := (1 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 4, 1} : Finset (Fin 6)) = {0, 1, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (4 : Fin 6))
        (c := (0 : Fin 6)) (d := (2 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 4, 0} : Finset (Fin 6)) = {0, 1, 4} from by decide] at h
    rw [show ({1, 4, 2} : Finset (Fin 6)) = {1, 2, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (4 : Fin 6))
        (c := (0 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 4, 0} : Finset (Fin 6)) = {0, 1, 4} from by decide] at h
    rw [show ({1, 4, 3} : Finset (Fin 6)) = {1, 3, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (4 : Fin 6))
        (c := (0 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 4, 0} : Finset (Fin 6)) = {0, 1, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (5 : Fin 6))
        (c := (1 : Fin 6)) (d := (2 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 5, 1} : Finset (Fin 6)) = {0, 1, 5} from by decide] at h
    rw [show ({0, 5, 2} : Finset (Fin 6)) = {0, 2, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (5 : Fin 6))
        (c := (1 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 5, 1} : Finset (Fin 6)) = {0, 1, 5} from by decide] at h
    rw [show ({0, 5, 3} : Finset (Fin 6)) = {0, 3, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (5 : Fin 6))
        (c := (1 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 5, 1} : Finset (Fin 6)) = {0, 1, 5} from by decide] at h
    rw [show ({0, 5, 4} : Finset (Fin 6)) = {0, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (5 : Fin 6))
        (c := (0 : Fin 6)) (d := (2 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 5, 0} : Finset (Fin 6)) = {0, 1, 5} from by decide] at h
    rw [show ({1, 5, 2} : Finset (Fin 6)) = {1, 2, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (5 : Fin 6))
        (c := (0 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 5, 0} : Finset (Fin 6)) = {0, 1, 5} from by decide] at h
    rw [show ({1, 5, 3} : Finset (Fin 6)) = {1, 3, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (5 : Fin 6))
        (c := (0 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 5, 0} : Finset (Fin 6)) = {0, 1, 5} from by decide] at h
    rw [show ({1, 5, 4} : Finset (Fin 6)) = {1, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (2 : Fin 6))
        (c := (3 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (2 : Fin 6))
        (c := (3 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (3 : Fin 6))
        (c := (2 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 3, 2} : Finset (Fin 6)) = {0, 2, 3} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (3 : Fin 6))
        (c := (2 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 3, 2} : Finset (Fin 6)) = {0, 2, 3} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (3 : Fin 6))
        (c := (0 : Fin 6)) (d := (1 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 3, 0} : Finset (Fin 6)) = {0, 2, 3} from by decide] at h
    rw [show ({2, 3, 1} : Finset (Fin 6)) = {1, 2, 3} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (3 : Fin 6))
        (c := (0 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 3, 0} : Finset (Fin 6)) = {0, 2, 3} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (3 : Fin 6))
        (c := (0 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 3, 0} : Finset (Fin 6)) = {0, 2, 3} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (2 : Fin 6))
        (c := (4 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (4 : Fin 6))
        (c := (2 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 4, 2} : Finset (Fin 6)) = {0, 2, 4} from by decide] at h
    rw [show ({0, 4, 3} : Finset (Fin 6)) = {0, 3, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (4 : Fin 6))
        (c := (2 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 4, 2} : Finset (Fin 6)) = {0, 2, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (4 : Fin 6))
        (c := (0 : Fin 6)) (d := (1 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 4, 0} : Finset (Fin 6)) = {0, 2, 4} from by decide] at h
    rw [show ({2, 4, 1} : Finset (Fin 6)) = {1, 2, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (4 : Fin 6))
        (c := (0 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 4, 0} : Finset (Fin 6)) = {0, 2, 4} from by decide] at h
    rw [show ({2, 4, 3} : Finset (Fin 6)) = {2, 3, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (4 : Fin 6))
        (c := (0 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 4, 0} : Finset (Fin 6)) = {0, 2, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (5 : Fin 6))
        (c := (2 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 5, 2} : Finset (Fin 6)) = {0, 2, 5} from by decide] at h
    rw [show ({0, 5, 3} : Finset (Fin 6)) = {0, 3, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (5 : Fin 6))
        (c := (2 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 5, 2} : Finset (Fin 6)) = {0, 2, 5} from by decide] at h
    rw [show ({0, 5, 4} : Finset (Fin 6)) = {0, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (5 : Fin 6))
        (c := (0 : Fin 6)) (d := (1 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 5, 0} : Finset (Fin 6)) = {0, 2, 5} from by decide] at h
    rw [show ({2, 5, 1} : Finset (Fin 6)) = {1, 2, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (5 : Fin 6))
        (c := (0 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 5, 0} : Finset (Fin 6)) = {0, 2, 5} from by decide] at h
    rw [show ({2, 5, 3} : Finset (Fin 6)) = {2, 3, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (5 : Fin 6))
        (c := (0 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 5, 0} : Finset (Fin 6)) = {0, 2, 5} from by decide] at h
    rw [show ({2, 5, 4} : Finset (Fin 6)) = {2, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (3 : Fin 6))
        (c := (4 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (4 : Fin 6))
        (c := (3 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 4, 3} : Finset (Fin 6)) = {0, 3, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (3 : Fin 6)) (j := (4 : Fin 6))
        (c := (0 : Fin 6)) (d := (1 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({3, 4, 0} : Finset (Fin 6)) = {0, 3, 4} from by decide] at h
    rw [show ({3, 4, 1} : Finset (Fin 6)) = {1, 3, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (3 : Fin 6)) (j := (4 : Fin 6))
        (c := (0 : Fin 6)) (d := (2 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({3, 4, 0} : Finset (Fin 6)) = {0, 3, 4} from by decide] at h
    rw [show ({3, 4, 2} : Finset (Fin 6)) = {2, 3, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (3 : Fin 6)) (j := (4 : Fin 6))
        (c := (0 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({3, 4, 0} : Finset (Fin 6)) = {0, 3, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (0 : Fin 6)) (j := (5 : Fin 6))
        (c := (3 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({0, 5, 3} : Finset (Fin 6)) = {0, 3, 5} from by decide] at h
    rw [show ({0, 5, 4} : Finset (Fin 6)) = {0, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (3 : Fin 6)) (j := (5 : Fin 6))
        (c := (0 : Fin 6)) (d := (1 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({3, 5, 0} : Finset (Fin 6)) = {0, 3, 5} from by decide] at h
    rw [show ({3, 5, 1} : Finset (Fin 6)) = {1, 3, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (3 : Fin 6)) (j := (5 : Fin 6))
        (c := (0 : Fin 6)) (d := (2 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({3, 5, 0} : Finset (Fin 6)) = {0, 3, 5} from by decide] at h
    rw [show ({3, 5, 2} : Finset (Fin 6)) = {2, 3, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (3 : Fin 6)) (j := (5 : Fin 6))
        (c := (0 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({3, 5, 0} : Finset (Fin 6)) = {0, 3, 5} from by decide] at h
    rw [show ({3, 5, 4} : Finset (Fin 6)) = {3, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (4 : Fin 6)) (j := (5 : Fin 6))
        (c := (0 : Fin 6)) (d := (1 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({4, 5, 0} : Finset (Fin 6)) = {0, 4, 5} from by decide] at h
    rw [show ({4, 5, 1} : Finset (Fin 6)) = {1, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (4 : Fin 6)) (j := (5 : Fin 6))
        (c := (0 : Fin 6)) (d := (2 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({4, 5, 0} : Finset (Fin 6)) = {0, 4, 5} from by decide] at h
    rw [show ({4, 5, 2} : Finset (Fin 6)) = {2, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (4 : Fin 6)) (j := (5 : Fin 6))
        (c := (0 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({4, 5, 0} : Finset (Fin 6)) = {0, 4, 5} from by decide] at h
    rw [show ({4, 5, 3} : Finset (Fin 6)) = {3, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (2 : Fin 6))
        (c := (3 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (2 : Fin 6))
        (c := (3 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (3 : Fin 6))
        (c := (2 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 3, 2} : Finset (Fin 6)) = {1, 2, 3} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (3 : Fin 6))
        (c := (2 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 3, 2} : Finset (Fin 6)) = {1, 2, 3} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (3 : Fin 6))
        (c := (1 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 3, 1} : Finset (Fin 6)) = {1, 2, 3} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (3 : Fin 6))
        (c := (1 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 3, 1} : Finset (Fin 6)) = {1, 2, 3} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (2 : Fin 6))
        (c := (4 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (4 : Fin 6))
        (c := (2 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 4, 2} : Finset (Fin 6)) = {1, 2, 4} from by decide] at h
    rw [show ({1, 4, 3} : Finset (Fin 6)) = {1, 3, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (4 : Fin 6))
        (c := (2 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 4, 2} : Finset (Fin 6)) = {1, 2, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (4 : Fin 6))
        (c := (1 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 4, 1} : Finset (Fin 6)) = {1, 2, 4} from by decide] at h
    rw [show ({2, 4, 3} : Finset (Fin 6)) = {2, 3, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (4 : Fin 6))
        (c := (1 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 4, 1} : Finset (Fin 6)) = {1, 2, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (5 : Fin 6))
        (c := (2 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 5, 2} : Finset (Fin 6)) = {1, 2, 5} from by decide] at h
    rw [show ({1, 5, 3} : Finset (Fin 6)) = {1, 3, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (5 : Fin 6))
        (c := (2 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 5, 2} : Finset (Fin 6)) = {1, 2, 5} from by decide] at h
    rw [show ({1, 5, 4} : Finset (Fin 6)) = {1, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (5 : Fin 6))
        (c := (1 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 5, 1} : Finset (Fin 6)) = {1, 2, 5} from by decide] at h
    rw [show ({2, 5, 3} : Finset (Fin 6)) = {2, 3, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (5 : Fin 6))
        (c := (1 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 5, 1} : Finset (Fin 6)) = {1, 2, 5} from by decide] at h
    rw [show ({2, 5, 4} : Finset (Fin 6)) = {2, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (3 : Fin 6))
        (c := (4 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (4 : Fin 6))
        (c := (3 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 4, 3} : Finset (Fin 6)) = {1, 3, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (3 : Fin 6)) (j := (4 : Fin 6))
        (c := (1 : Fin 6)) (d := (2 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({3, 4, 1} : Finset (Fin 6)) = {1, 3, 4} from by decide] at h
    rw [show ({3, 4, 2} : Finset (Fin 6)) = {2, 3, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (3 : Fin 6)) (j := (4 : Fin 6))
        (c := (1 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({3, 4, 1} : Finset (Fin 6)) = {1, 3, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (1 : Fin 6)) (j := (5 : Fin 6))
        (c := (3 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({1, 5, 3} : Finset (Fin 6)) = {1, 3, 5} from by decide] at h
    rw [show ({1, 5, 4} : Finset (Fin 6)) = {1, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (3 : Fin 6)) (j := (5 : Fin 6))
        (c := (1 : Fin 6)) (d := (2 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({3, 5, 1} : Finset (Fin 6)) = {1, 3, 5} from by decide] at h
    rw [show ({3, 5, 2} : Finset (Fin 6)) = {2, 3, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (3 : Fin 6)) (j := (5 : Fin 6))
        (c := (1 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({3, 5, 1} : Finset (Fin 6)) = {1, 3, 5} from by decide] at h
    rw [show ({3, 5, 4} : Finset (Fin 6)) = {3, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (4 : Fin 6)) (j := (5 : Fin 6))
        (c := (1 : Fin 6)) (d := (2 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({4, 5, 1} : Finset (Fin 6)) = {1, 4, 5} from by decide] at h
    rw [show ({4, 5, 2} : Finset (Fin 6)) = {2, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (4 : Fin 6)) (j := (5 : Fin 6))
        (c := (1 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({4, 5, 1} : Finset (Fin 6)) = {1, 4, 5} from by decide] at h
    rw [show ({4, 5, 3} : Finset (Fin 6)) = {3, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (3 : Fin 6))
        (c := (4 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (4 : Fin 6))
        (c := (3 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 4, 3} : Finset (Fin 6)) = {2, 3, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (3 : Fin 6)) (j := (4 : Fin 6))
        (c := (2 : Fin 6)) (d := (5 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({3, 4, 2} : Finset (Fin 6)) = {2, 3, 4} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (2 : Fin 6)) (j := (5 : Fin 6))
        (c := (3 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({2, 5, 3} : Finset (Fin 6)) = {2, 3, 5} from by decide] at h
    rw [show ({2, 5, 4} : Finset (Fin 6)) = {2, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (3 : Fin 6)) (j := (5 : Fin 6))
        (c := (2 : Fin 6)) (d := (4 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({3, 5, 2} : Finset (Fin 6)) = {2, 3, 5} from by decide] at h
    rw [show ({3, 5, 4} : Finset (Fin 6)) = {3, 4, 5} from by decide] at h
    exact h
  · have h :=
      not_both_sixPointBad_of_shared_pair
        M hLoopless hE hRank hStrict order
        (i := (4 : Fin 6)) (j := (5 : Fin 6))
        (c := (2 : Fin 6)) (d := (3 : Fin 6))
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    rw [show ({4, 5, 2} : Finset (Fin 6)) = {2, 4, 5} from by decide] at h
    rw [show ({4, 5, 3} : Finset (Fin 6)) = {3, 4, 5} from by decide] at h
    exact h

set_option maxHeartbeats 1000000 in
/-- A certified good alternative produces a cyclic basis order. -/
theorem exists_cyclicBasisOrder3_of_sixPointGoodAlternatives
    (M : Matroid α)
    (enum : Fin 6 ≃ M.E)
    (hGood :
      SixPointGoodAlternatives
        (SixPointBad M enum)) :
    ∃ order : Fin 6 ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  classical
  rcases hGood with h | h | h | h | h | h | h | h
  · refine ⟨sixPointPerm1.trans enum, ?_⟩
    obtain ⟨g0, g1, g2, g3, g4, g5⟩ := h
    intro i
    fin_cases i
    · simpa [SixPointBad, finSixSet, sixPointPerm1_apply, cyclicIndex,
        Set.image_insert_eq, Set.image_singleton] using g0
    · simpa [SixPointBad, finSixSet, sixPointPerm1_apply, cyclicIndex,
        Set.image_insert_eq, Set.image_singleton] using g1
    · simpa [SixPointBad, finSixSet, sixPointPerm1_apply, cyclicIndex,
        Set.image_insert_eq, Set.image_singleton] using g2
    · simpa [SixPointBad, finSixSet, sixPointPerm1_apply, cyclicIndex,
        Set.image_insert_eq, Set.image_singleton] using g3
    · have hb : M.IsBase ({(enum 0 : α), (enum 4 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g4
      have hgoal : M.IsBase ({(enum 4 : α), (enum 5 : α), (enum 0 : α)} : Set α) := by
        rw [show ({(enum 4 : α), (enum 5 : α), (enum 0 : α)} : Set α)
              = {(enum 0 : α), (enum 4 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm1_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 0 : α), (enum 1 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g5
      have hgoal : M.IsBase ({(enum 5 : α), (enum 0 : α), (enum 1 : α)} : Set α) := by
        rw [show ({(enum 5 : α), (enum 0 : α), (enum 1 : α)} : Set α)
              = {(enum 0 : α), (enum 1 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm1_apply, cyclicIndex] using hgoal
  · refine ⟨sixPointPerm2.trans enum, ?_⟩
    obtain ⟨g0, g1, g2, g3, g4, g5⟩ := h
    intro i
    fin_cases i
    · simpa [SixPointBad, finSixSet, sixPointPerm2_apply, cyclicIndex,
        Set.image_insert_eq, Set.image_singleton] using g0
    · have hb : M.IsBase ({(enum 1 : α), (enum 2 : α), (enum 4 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g1
      have hgoal : M.IsBase ({(enum 2 : α), (enum 4 : α), (enum 1 : α)} : Set α) := by
        rw [show ({(enum 2 : α), (enum 4 : α), (enum 1 : α)} : Set α)
              = {(enum 1 : α), (enum 2 : α), (enum 4 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm2_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 1 : α), (enum 4 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g2
      have hgoal : M.IsBase ({(enum 4 : α), (enum 1 : α), (enum 5 : α)} : Set α) := by
        rw [show ({(enum 4 : α), (enum 1 : α), (enum 5 : α)} : Set α)
              = {(enum 1 : α), (enum 4 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm2_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 1 : α), (enum 3 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g3
      have hgoal : M.IsBase ({(enum 1 : α), (enum 5 : α), (enum 3 : α)} : Set α) := by
        rw [show ({(enum 1 : α), (enum 5 : α), (enum 3 : α)} : Set α)
              = {(enum 1 : α), (enum 3 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm2_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 0 : α), (enum 3 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g4
      have hgoal : M.IsBase ({(enum 5 : α), (enum 3 : α), (enum 0 : α)} : Set α) := by
        rw [show ({(enum 5 : α), (enum 3 : α), (enum 0 : α)} : Set α)
              = {(enum 0 : α), (enum 3 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm2_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 0 : α), (enum 2 : α), (enum 3 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g5
      have hgoal : M.IsBase ({(enum 3 : α), (enum 0 : α), (enum 2 : α)} : Set α) := by
        rw [show ({(enum 3 : α), (enum 0 : α), (enum 2 : α)} : Set α)
              = {(enum 0 : α), (enum 2 : α), (enum 3 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm2_apply, cyclicIndex] using hgoal
  · refine ⟨sixPointPerm3.trans enum, ?_⟩
    obtain ⟨g0, g1, g2, g3, g4, g5⟩ := h
    intro i
    fin_cases i
    · simpa [SixPointBad, finSixSet, sixPointPerm3_apply, cyclicIndex,
        Set.image_insert_eq, Set.image_singleton] using g0
    · simpa [SixPointBad, finSixSet, sixPointPerm3_apply, cyclicIndex,
        Set.image_insert_eq, Set.image_singleton] using g1
    · have hb : M.IsBase ({(enum 2 : α), (enum 4 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g2
      have hgoal : M.IsBase ({(enum 2 : α), (enum 5 : α), (enum 4 : α)} : Set α) := by
        rw [show ({(enum 2 : α), (enum 5 : α), (enum 4 : α)} : Set α)
              = {(enum 2 : α), (enum 4 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm3_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 3 : α), (enum 4 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g3
      have hgoal : M.IsBase ({(enum 5 : α), (enum 4 : α), (enum 3 : α)} : Set α) := by
        rw [show ({(enum 5 : α), (enum 4 : α), (enum 3 : α)} : Set α)
              = {(enum 3 : α), (enum 4 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm3_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 0 : α), (enum 3 : α), (enum 4 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g4
      have hgoal : M.IsBase ({(enum 4 : α), (enum 3 : α), (enum 0 : α)} : Set α) := by
        rw [show ({(enum 4 : α), (enum 3 : α), (enum 0 : α)} : Set α)
              = {(enum 0 : α), (enum 3 : α), (enum 4 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm3_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 0 : α), (enum 1 : α), (enum 3 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g5
      have hgoal : M.IsBase ({(enum 3 : α), (enum 0 : α), (enum 1 : α)} : Set α) := by
        rw [show ({(enum 3 : α), (enum 0 : α), (enum 1 : α)} : Set α)
              = {(enum 0 : α), (enum 1 : α), (enum 3 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm3_apply, cyclicIndex] using hgoal
  · refine ⟨sixPointPerm4.trans enum, ?_⟩
    obtain ⟨g0, g1, g2, g3, g4, g5⟩ := h
    intro i
    fin_cases i
    · have hb : M.IsBase ({(enum 0 : α), (enum 1 : α), (enum 4 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g0
      have hgoal : M.IsBase ({(enum 0 : α), (enum 4 : α), (enum 1 : α)} : Set α) := by
        rw [show ({(enum 0 : α), (enum 4 : α), (enum 1 : α)} : Set α)
              = {(enum 0 : α), (enum 1 : α), (enum 4 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm4_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 1 : α), (enum 3 : α), (enum 4 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g1
      have hgoal : M.IsBase ({(enum 4 : α), (enum 1 : α), (enum 3 : α)} : Set α) := by
        rw [show ({(enum 4 : α), (enum 1 : α), (enum 3 : α)} : Set α)
              = {(enum 1 : α), (enum 3 : α), (enum 4 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm4_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 1 : α), (enum 2 : α), (enum 3 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g2
      have hgoal : M.IsBase ({(enum 1 : α), (enum 3 : α), (enum 2 : α)} : Set α) := by
        rw [show ({(enum 1 : α), (enum 3 : α), (enum 2 : α)} : Set α)
              = {(enum 1 : α), (enum 2 : α), (enum 3 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm4_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 2 : α), (enum 3 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g3
      have hgoal : M.IsBase ({(enum 3 : α), (enum 2 : α), (enum 5 : α)} : Set α) := by
        rw [show ({(enum 3 : α), (enum 2 : α), (enum 5 : α)} : Set α)
              = {(enum 2 : α), (enum 3 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm4_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 0 : α), (enum 2 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g4
      have hgoal : M.IsBase ({(enum 2 : α), (enum 5 : α), (enum 0 : α)} : Set α) := by
        rw [show ({(enum 2 : α), (enum 5 : α), (enum 0 : α)} : Set α)
              = {(enum 0 : α), (enum 2 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm4_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 0 : α), (enum 4 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g5
      have hgoal : M.IsBase ({(enum 5 : α), (enum 0 : α), (enum 4 : α)} : Set α) := by
        rw [show ({(enum 5 : α), (enum 0 : α), (enum 4 : α)} : Set α)
              = {(enum 0 : α), (enum 4 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm4_apply, cyclicIndex] using hgoal
  · refine ⟨sixPointPerm5.trans enum, ?_⟩
    obtain ⟨g0, g1, g2, g3, g4, g5⟩ := h
    intro i
    fin_cases i
    · simpa [SixPointBad, finSixSet, sixPointPerm5_apply, cyclicIndex,
        Set.image_insert_eq, Set.image_singleton] using g0
    · have hb : M.IsBase ({(enum 1 : α), (enum 3 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g1
      have hgoal : M.IsBase ({(enum 1 : α), (enum 5 : α), (enum 3 : α)} : Set α) := by
        rw [show ({(enum 1 : α), (enum 5 : α), (enum 3 : α)} : Set α)
              = {(enum 1 : α), (enum 3 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm5_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 2 : α), (enum 3 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g2
      have hgoal : M.IsBase ({(enum 5 : α), (enum 3 : α), (enum 2 : α)} : Set α) := by
        rw [show ({(enum 5 : α), (enum 3 : α), (enum 2 : α)} : Set α)
              = {(enum 2 : α), (enum 3 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm5_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 2 : α), (enum 3 : α), (enum 4 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g3
      have hgoal : M.IsBase ({(enum 3 : α), (enum 2 : α), (enum 4 : α)} : Set α) := by
        rw [show ({(enum 3 : α), (enum 2 : α), (enum 4 : α)} : Set α)
              = {(enum 2 : α), (enum 3 : α), (enum 4 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm5_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 0 : α), (enum 2 : α), (enum 4 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g4
      have hgoal : M.IsBase ({(enum 2 : α), (enum 4 : α), (enum 0 : α)} : Set α) := by
        rw [show ({(enum 2 : α), (enum 4 : α), (enum 0 : α)} : Set α)
              = {(enum 0 : α), (enum 2 : α), (enum 4 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm5_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 0 : α), (enum 1 : α), (enum 4 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g5
      have hgoal : M.IsBase ({(enum 4 : α), (enum 0 : α), (enum 1 : α)} : Set α) := by
        rw [show ({(enum 4 : α), (enum 0 : α), (enum 1 : α)} : Set α)
              = {(enum 0 : α), (enum 1 : α), (enum 4 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm5_apply, cyclicIndex] using hgoal
  · refine ⟨sixPointPerm6.trans enum, ?_⟩
    obtain ⟨g0, g1, g2, g3, g4, g5⟩ := h
    intro i
    fin_cases i
    · have hb : M.IsBase ({(enum 0 : α), (enum 1 : α), (enum 3 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g0
      have hgoal : M.IsBase ({(enum 0 : α), (enum 3 : α), (enum 1 : α)} : Set α) := by
        rw [show ({(enum 0 : α), (enum 3 : α), (enum 1 : α)} : Set α)
              = {(enum 0 : α), (enum 1 : α), (enum 3 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm6_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 1 : α), (enum 3 : α), (enum 4 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g1
      have hgoal : M.IsBase ({(enum 3 : α), (enum 1 : α), (enum 4 : α)} : Set α) := by
        rw [show ({(enum 3 : α), (enum 1 : α), (enum 4 : α)} : Set α)
              = {(enum 1 : α), (enum 3 : α), (enum 4 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm6_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 1 : α), (enum 2 : α), (enum 4 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g2
      have hgoal : M.IsBase ({(enum 1 : α), (enum 4 : α), (enum 2 : α)} : Set α) := by
        rw [show ({(enum 1 : α), (enum 4 : α), (enum 2 : α)} : Set α)
              = {(enum 1 : α), (enum 2 : α), (enum 4 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm6_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 2 : α), (enum 4 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g3
      have hgoal : M.IsBase ({(enum 4 : α), (enum 2 : α), (enum 5 : α)} : Set α) := by
        rw [show ({(enum 4 : α), (enum 2 : α), (enum 5 : α)} : Set α)
              = {(enum 2 : α), (enum 4 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm6_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 0 : α), (enum 2 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g4
      have hgoal : M.IsBase ({(enum 2 : α), (enum 5 : α), (enum 0 : α)} : Set α) := by
        rw [show ({(enum 2 : α), (enum 5 : α), (enum 0 : α)} : Set α)
              = {(enum 0 : α), (enum 2 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm6_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 0 : α), (enum 3 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g5
      have hgoal : M.IsBase ({(enum 5 : α), (enum 0 : α), (enum 3 : α)} : Set α) := by
        rw [show ({(enum 5 : α), (enum 0 : α), (enum 3 : α)} : Set α)
              = {(enum 0 : α), (enum 3 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm6_apply, cyclicIndex] using hgoal
  · refine ⟨sixPointPerm7.trans enum, ?_⟩
    obtain ⟨g0, g1, g2, g3, g4, g5⟩ := h
    intro i
    fin_cases i
    · have hb : M.IsBase ({(enum 0 : α), (enum 1 : α), (enum 2 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g0
      have hgoal : M.IsBase ({(enum 0 : α), (enum 2 : α), (enum 1 : α)} : Set α) := by
        rw [show ({(enum 0 : α), (enum 2 : α), (enum 1 : α)} : Set α)
              = {(enum 0 : α), (enum 1 : α), (enum 2 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm7_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 1 : α), (enum 2 : α), (enum 3 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g1
      have hgoal : M.IsBase ({(enum 2 : α), (enum 1 : α), (enum 3 : α)} : Set α) := by
        rw [show ({(enum 2 : α), (enum 1 : α), (enum 3 : α)} : Set α)
              = {(enum 1 : α), (enum 2 : α), (enum 3 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm7_apply, cyclicIndex] using hgoal
    · simpa [SixPointBad, finSixSet, sixPointPerm7_apply, cyclicIndex,
        Set.image_insert_eq, Set.image_singleton] using g2
    · have hb : M.IsBase ({(enum 3 : α), (enum 4 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g3
      have hgoal : M.IsBase ({(enum 3 : α), (enum 5 : α), (enum 4 : α)} : Set α) := by
        rw [show ({(enum 3 : α), (enum 5 : α), (enum 4 : α)} : Set α)
              = {(enum 3 : α), (enum 4 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm7_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 0 : α), (enum 4 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g4
      have hgoal : M.IsBase ({(enum 5 : α), (enum 4 : α), (enum 0 : α)} : Set α) := by
        rw [show ({(enum 5 : α), (enum 4 : α), (enum 0 : α)} : Set α)
              = {(enum 0 : α), (enum 4 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm7_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 0 : α), (enum 2 : α), (enum 4 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g5
      have hgoal : M.IsBase ({(enum 4 : α), (enum 0 : α), (enum 2 : α)} : Set α) := by
        rw [show ({(enum 4 : α), (enum 0 : α), (enum 2 : α)} : Set α)
              = {(enum 0 : α), (enum 2 : α), (enum 4 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm7_apply, cyclicIndex] using hgoal
  · refine ⟨sixPointPerm8.trans enum, ?_⟩
    obtain ⟨g0, g1, g2, g3, g4, g5⟩ := h
    intro i
    fin_cases i
    · simpa [SixPointBad, finSixSet, sixPointPerm8_apply, cyclicIndex,
        Set.image_insert_eq, Set.image_singleton] using g0
    · have hb : M.IsBase ({(enum 1 : α), (enum 3 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g1
      have hgoal : M.IsBase ({(enum 1 : α), (enum 5 : α), (enum 3 : α)} : Set α) := by
        rw [show ({(enum 1 : α), (enum 5 : α), (enum 3 : α)} : Set α)
              = {(enum 1 : α), (enum 3 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm8_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 3 : α), (enum 4 : α), (enum 5 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g2
      have hgoal : M.IsBase ({(enum 5 : α), (enum 3 : α), (enum 4 : α)} : Set α) := by
        rw [show ({(enum 5 : α), (enum 3 : α), (enum 4 : α)} : Set α)
              = {(enum 3 : α), (enum 4 : α), (enum 5 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm8_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 2 : α), (enum 3 : α), (enum 4 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g3
      have hgoal : M.IsBase ({(enum 3 : α), (enum 4 : α), (enum 2 : α)} : Set α) := by
        rw [show ({(enum 3 : α), (enum 4 : α), (enum 2 : α)} : Set α)
              = {(enum 2 : α), (enum 3 : α), (enum 4 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm8_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 0 : α), (enum 2 : α), (enum 4 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g4
      have hgoal : M.IsBase ({(enum 4 : α), (enum 2 : α), (enum 0 : α)} : Set α) := by
        rw [show ({(enum 4 : α), (enum 2 : α), (enum 0 : α)} : Set α)
              = {(enum 0 : α), (enum 2 : α), (enum 4 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm8_apply, cyclicIndex] using hgoal
    · have hb : M.IsBase ({(enum 0 : α), (enum 1 : α), (enum 2 : α)} : Set α) := by
        simpa [SixPointBad, finSixSet,
          Set.image_insert_eq, Set.image_singleton] using g5
      have hgoal : M.IsBase ({(enum 2 : α), (enum 0 : α), (enum 1 : α)} : Set α) := by
        rw [show ({(enum 2 : α), (enum 0 : α), (enum 1 : α)} : Set α)
              = {(enum 0 : α), (enum 1 : α), (enum 2 : α)} from by
          ext w
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto]
        exact hb
      simpa [sixPointPerm8_apply, cyclicIndex] using hgoal

/-- The strict six-element rank-three case has a cyclic basis order. -/
theorem exists_cyclicBasisOrder3_of_strict_two
    (M : Matroid α)
    (hLoopless : M.Loopless)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = (6 : ℕ∞))
    (hStrict : StrictlyUniformlyDense M 2) :
    ∃ order : Fin 6 ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hEncard : M.E.ncard = 6 := by
    have hcast : (M.E.ncard : ℕ∞) = (6 : ℕ∞) := by
      rw [hE.cast_ncard_eq]
      exact hEcard
    exact_mod_cast hcast
  let : Fintype M.E := hE.fintype
  have hNatCard : Nat.card M.E = 6 := by
    simpa only [Nat.card_coe_set_eq] using hEncard
  let enum : Fin 6 ≃ M.E :=
    (Finite.equivFinOfCardEq hNatCard).symm
  have hLinear :
      LinearSixBad (SixPointBad M enum) :=
    linearSixBad_of_strict_two
      M hLoopless hE hRank hStrict enum
  have hGood :
      SixPointGoodAlternatives
        (SixPointBad M enum) :=
    sixPointGoodAlternatives_of_linear
      (SixPointBad M enum) hLinear
  exact
    exists_cyclicBasisOrder3_of_sixPointGoodAlternatives
      M enum hGood

/-- The complete six-element uniformly dense rank-three case. -/
theorem exists_cyclicBasisOrder3_of_ground_encard_six
    (M : Matroid α)
    (hE : M.E.Finite)
    (hRank : M.eRank = 3)
    (hEcard : M.E.encard = (6 : ℕ∞))
    (hDense : UniformlyDense M 2) :
    ∃ order : Fin 6 ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  have hLoopless : M.Loopless :=
    loopless_of_uniformlyDense M 2 (by omega) hDense
  apply
    exists_cyclicBasisOrder3_of_strict_case
      M 2 (by omega) hE hRank
      (by simpa using hEcard) hDense
  intro hStrict
  simpa using
    exists_cyclicBasisOrder3_of_strict_two
      M hLoopless hE hRank hEcard hStrict

#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_strict_two
#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_ground_encard_six

#print axioms Rank3KUM.exists_cyclicBasisOrder3_of_sixPointGoodAlternatives

#print axioms Rank3KUM.linearSixBad_of_strict_two

#print axioms Rank3KUM.not_both_sixPointBad_of_shared_pair

#print axioms Rank3KUM.false_of_two_nonbase_triples_sharing_pair_strict_two

#print axioms Rank3KUM.pair_indep_of_strict_two

end Rank3KUM
