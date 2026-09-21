import HigherRankKUM.PeriodicGluing
import HigherRankKUM.BalancedGluing

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/--
Regression theorem: the original balanced restriction/contraction gluing
statement is the denominator-one (`q=1`) specialization of periodic gluing.
The original theorem is retained unchanged; this theorem certifies semantic
compatibility between the old and new combinatorial layers.
-/
theorem exists_cyclicBasisOrder_of_balanced_restrict_contract_via_periodic
    (M : Matroid α) {X : Set α} {s t k : ℕ}
    (hs : 0 < s) (ht : 0 < t) (hk : 0 < k)
    (hX : X ⊆ M.E)
    (σS : Fin (s * k) ≃ (Matroid.restrict M X).E)
    (σT : Fin (t * k) ≃ (Matroid.contract M X).E)
    (hS : CyclicBasisOrder (Matroid.restrict M X) s
      (Nat.mul_pos hs hk) σS)
    (hT : CyclicBasisOrder (Matroid.contract M X) t
      (Nat.mul_pos ht hk) σT) :
    ∃ σ : Fin ((s + t) * k) ≃ M.E,
      CyclicBasisOrder M (s + t)
        (Nat.mul_pos (by omega) hk) σ := by
  have h :=
    exists_cyclicBasisOrder_of_periodic_restrict_contract
      (M := M) (X := X) (a := s) (b := t) (p := k) (q := 1)
      hs ht hk hX σS σT
      (by simpa using hS) (by simpa using hT)
  simpa using h

end

end HigherRankKUM
