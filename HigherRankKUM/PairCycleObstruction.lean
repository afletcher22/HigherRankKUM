import HigherRankKUM.AdmissiblePairCycle
import Mathlib.Data.Nat.ModEq

namespace HigherRankKUM
namespace PairCycleObstruction

open BinaryRelationCycle

/-- Multiplication by `h` modulo `N`; this enumerates the orbit of repeated
`+h` from zero when `gcd(N,h)=1`. -/
def stepIndex (N h : ℕ) (hN : 0 < N) (j : Fin N) : Fin N :=
  ⟨(j.val * h) % N, Nat.mod_lt _ hN⟩

@[simp] lemma stepIndex_val (N h : ℕ) (hN : 0 < N) (j : Fin N) :
    (stepIndex N h hN j).val = (j.val * h) % N := rfl

/-- Coprimality makes the successor-orbit enumeration injective. -/
theorem stepIndex_injective {N h : ℕ} (hN : 0 < N)
    (hcop : Nat.gcd N h = 1) :
    Function.Injective (stepIndex N h hN) := by
  intro i j hij
  apply Fin.ext
  have hmod : i.val * h ≡ j.val * h [MOD N] := by
    change (i.val * h) % N = (j.val * h) % N
    exact congrArg Fin.val hij
  exact (Nat.ModEq.cancel_right_of_coprime hcop hmod).eq_of_lt_of_lt i.isLt j.isLt

/-- Hence `j ↦ jh (mod N)` is an equivalence of pair indices. -/
noncomputable def stepEquiv (N h : ℕ) (hN : 0 < N) (hcop : Nat.gcd N h = 1) :
    Fin N ≃ Fin N :=
  Equiv.ofBijective (stepIndex N h hN)
    ⟨stepIndex_injective hN hcop,
      (Finite.injective_iff_surjective.mp (stepIndex_injective hN hcop))⟩

/-- The local relations listed in the single `+h` successor orbit. -/
def relationCycleList (N h : ℕ) (hN : 0 < N)
    (R : Fin N → Relation) : List Relation :=
  List.ofFn fun j : Fin N => R (stepIndex N h hN j)

/-- Orientability of the fixed pair cycle at the level of its local Boolean
relations.  The gcd hypothesis is not part of the definition; it is used to
identify this list with all pair indices exactly once. -/
def PairRelationOrientable (N h : ℕ) (hN : 0 < N)
    (R : Fin N → Relation) : Prop :=
  CyclicSatisfiable (relationCycleList N h hN R)

lemma relationCycleList_mem_fullSupport {N h : ℕ} (hN : 0 < N)
    {R : Fin N → Relation} (hfull : ∀ i, FullSupport (R i)) :
    ∀ S ∈ relationCycleList N h hN R, FullSupport S := by
  intro S hS
  simp [relationCycleList] at hS
  obtain ⟨j, rfl⟩ := hS
  exact hfull _

/-- Global forced-transition characterization in successor order.  If the
fixed pair cycle is not orientable, every local relation is a bijection and
the composed transition has no fixed point. -/
theorem not_orientable_iff_forced_no_fixed_point
    {N h : ℕ} (hN : 0 < N) (hcop : Nat.gcd N h = 1)
    {R : Fin N → Relation} (hfull : ∀ i, FullSupport (R i)) :
    ¬ PairRelationOrientable N h hN R ↔
      (∀ i, BijectionRelation (R i)) ∧
      (¬ ∃ x, composeList (relationCycleList N h hN R) x x) := by
  have hlistFull := relationCycleList_mem_fullSupport (h := h) hN hfull
  rw [PairRelationOrientable, not_cyclicSatisfiable_iff hlistFull]
  constructor
  · rintro ⟨hall, hfix⟩
    refine ⟨?_, hfix⟩
    intro i
    have hsurj : Function.Surjective (stepIndex N h hN) :=
      Finite.injective_iff_surjective.mp (stepIndex_injective hN hcop)
    obtain ⟨j, hj⟩ := hsurj i
    have hmem : R (stepIndex N h hN j) ∈ relationCycleList N h hN R := by
      simp [relationCycleList]
    rw [hj] at hmem
    exact hall (R i) hmem
  · rintro ⟨hall, hfix⟩
    exact ⟨fun S hS => by
      simp [relationCycleList] at hS
      obtain ⟨j, rfl⟩ := hS
      exact hall _, hfix⟩

/-- In particular, one local full-support relation with slack makes the fixed
pair cycle orientable. -/
theorem orientable_of_local_slack
    {N h : ℕ} (hN : 0 < N) (hcop : Nat.gcd N h = 1)
    {R : Fin N → Relation} (hfull : ∀ i, FullSupport (R i))
    (hslack : ∃ i, ¬ BijectionRelation (R i)) :
    PairRelationOrientable N h hN R := by
  by_contra hnot
  have hforced := (not_orientable_iff_forced_no_fixed_point hN hcop hfull).1 hnot
  obtain ⟨i, hi⟩ := hslack
  exact hi (hforced.1 i)

/-- Matroid application: for an exact admissible pair cycle in the nontrivial
range, the only fixed-cycle orientation obstruction is a forced Boolean
transition at every pair whose total successor-cycle composition has no fixed
point. -/
theorem admissible_pair_cycle_not_orientable_iff
    {α : Type*} {M : Matroid α} {N h : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N h hN)
    (hh : 0 < h) (hhN : h < N) (hcop : Nat.gcd N h = 1) :
    ¬ PairRelationOrientable N h hN (A.localRelation hh) ↔
      (∀ i, BijectionRelation (A.localRelation hh i)) ∧
      (¬ ∃ x,
        composeList (relationCycleList N h hN (A.localRelation hh)) x x) := by
  exact not_orientable_iff_forced_no_fixed_point hN hcop
    (A.localRelation_fullSupport hh hhN)

/-- Matroid corollary: a single local relation with slack makes the given
admissible pair cycle orientable at the compatibility-relation level. -/
theorem admissible_pair_cycle_orientable_of_local_slack
    {α : Type*} {M : Matroid α} {N h : ℕ} {hN : 0 < N}
    (A : AdmissiblePairCycle.Data M N h hN)
    (hh : 0 < h) (hhN : h < N) (hcop : Nat.gcd N h = 1)
    (hslack : ∃ i, ¬ BijectionRelation (A.localRelation hh i)) :
    PairRelationOrientable N h hN (A.localRelation hh) := by
  exact orientable_of_local_slack hN hcop
    (A.localRelation_fullSupport hh hhN) hslack

end PairCycleObstruction
end HigherRankKUM
