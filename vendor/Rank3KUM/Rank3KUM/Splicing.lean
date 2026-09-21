import Rank3KUM.SpliceWrap
import Rank3KUM.CyclicRotate

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/--
**SP — Contiguous basis splicing.** A cyclic rank-three basis order of a
rank-preserving deletion, of length at least six, admits contiguous insertion
of the deleted three-element basis.
-/
theorem contiguousBasisSplicing
    (M : Matroid α) {D : Set α} {m : ℕ}
    (hRank : M.eRank = 3)
    (hD : M.IsBase D)
    (hDelRank : (Matroid.delete M D).eRank = 3)
    (hm : 6 ≤ m)
    (small : Fin m ≃ (Matroid.delete M D).E)
    (hsmall :
      CyclicBasisOrder3 (Matroid.delete M D) (by omega) small) :
    ∃ order : Fin (m + 3) ≃ M.E,
      CyclicBasisOrder3 M (by omega) order := by
  let ip : Fin m := ⟨m - 2, by omega⟩
  let ia : Fin m := ⟨m - 1, by omega⟩
  let ib : Fin m := ⟨0, by omega⟩
  let ic : Fin m := ⟨1, by omega⟩
  let iq : Fin m := ⟨2, by omega⟩
  let p : α := (small ip : α)
  let a : α := (small ia : α)
  let b : α := (small ib : α)
  let c : α := (small ic : α)
  let q : α := (small iq : α)

  have hsmallM : CyclicBasisOrder3 M (by omega) small := by
    intro i
    exact isBase_of_delete_isBase_rank3 M hRank hDelRank (hsmall i)

  have hne {i j : Fin m} (hij : i ≠ j) :
      (small i : α) ≠ (small j : α) := by
    intro h
    apply hij
    apply small.injective
    apply Subtype.ext
    exact h
  have hipa : ip ≠ ia := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [ip, ia] at hv
    omega
  have hipb : ip ≠ ib := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [ip, ib] at hv
    omega
  have hipc : ip ≠ ic := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [ip, ic] at hv
    omega
  have hipq : ip ≠ iq := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [ip, iq] at hv
    omega
  have hiab : ia ≠ ib := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [ia, ib] at hv
    omega
  have hiac : ia ≠ ic := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [ia, ic] at hv
    omega
  have hiaq : ia ≠ iq := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [ia, iq] at hv
    omega
  have hibc : ib ≠ ic := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [ib, ic] at hv
    omega
  have hibq : ib ≠ iq := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [ib, iq] at hv
    omega
  have hicq : ic ≠ iq := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [ic, iq] at hv
    omega

  have hpa : p ≠ a := by simpa [p, a] using hne hipa
  have hpb : p ≠ b := by simpa [p, b] using hne hipb
  have hpc : p ≠ c := by simpa [p, c] using hne hipc
  have hpq : p ≠ q := by simpa [p, q] using hne hipq
  have hab : a ≠ b := by simpa [a, b] using hne hiab
  have hac : a ≠ c := by simpa [a, c] using hne hiac
  have haq : a ≠ q := by simpa [a, q] using hne hiaq
  have hbc : b ≠ c := by simpa [b, c] using hne hibc
  have hbq : b ≠ q := by simpa [b, q] using hne hibq
  have hcq : c ≠ q := by simpa [c, q] using hne hicq

  have hdistinct : List.Pairwise (· ≠ ·) [p, a, b, c, q] := by
    simp [hpa, hpb, hpc, hpq, hab, hac, haq, hbc, hbq, hcq]

  have hout (i : Fin m) : (small i : α) ∈ M.E \ D := by
    simp [Matroid.delete_ground]
  have hpOut : p ∈ M.E \ D := by simp [p]
  have haOut : a ∈ M.E \ D := by simp [a]
  have hbOut : b ∈ M.E \ D := by simp [b]
  have hcOut : c ∈ M.E \ D := by simp [c]
  have hqOut : q ∈ M.E \ D := by simp [q]

  have hip₁ : cyclicIndex m (by omega) ip 1 = ia := by
    apply Fin.ext
    change (m - 2 + 1) % m = m - 1
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hip₂ : cyclicIndex m (by omega) ip 2 = ib := by
    apply Fin.ext
    change (m - 2 + 2) % m = 0
    rw [show m - 2 + 2 = m by omega, Nat.mod_self]
  have hia₁ : cyclicIndex m (by omega) ia 1 = ib := by
    apply Fin.ext
    change (m - 1 + 1) % m = 0
    rw [show m - 1 + 1 = m by omega, Nat.mod_self]
  have hia₂ : cyclicIndex m (by omega) ia 2 = ic := by
    apply Fin.ext
    change (m - 1 + 2) % m = 1
    rw [show m - 1 + 2 = m + 1 by omega]
    simp [Nat.mod_eq_of_lt (by omega : 1 < m)]
  have hib₁ : cyclicIndex m (by omega) ib 1 = ic := by
    apply Fin.ext
    change (0 + 1) % m = 1
    rw [Nat.mod_eq_of_lt (by omega)]
  have hib₂ : cyclicIndex m (by omega) ib 2 = iq := by
    apply Fin.ext
    change (0 + 2) % m = 2
    rw [Nat.mod_eq_of_lt (by omega)]

  have hP : M.IsBase ({p, a, b} : Set α) := by
    have hs := hsmallM ip
    rw [hip₁, hip₂] at hs
    simpa [p, a, b] using hs
  have hC : M.IsBase ({a, b, c} : Set α) := by
    have hs := hsmallM ia
    rw [hia₁, hia₂] at hs
    simpa [a, b, c] using hs
  have hQ : M.IsBase ({b, c, q} : Set α) := by
    have hs := hsmallM ib
    rw [hib₁, hib₂] at hs
    simpa [b, c, q] using hs

  have hTG : TwoGap.TwoGapConclusion M D p a b c q :=
    TwoGap.universalTwoGapInsertion M hRank hD hdistinct
      hpOut haOut hbOut hcOut hqOut hP hC hQ

  have hED : Disjoint (Matroid.delete M D).E D := by
    rw [Matroid.delete_ground]
    exact disjoint_sdiff_left
  have hUnion : (Matroid.delete M D).E ∪ D = M.E := by
    rw [Matroid.delete_ground]
    exact sdiff_union_of_subset hD.subset_ground

  rcases hTG with hFirst | hSecond
  · rcases hFirst with ⟨block, h₁, h₂, h₃, h₄⟩
    have hApp :
        CyclicBasisOrder3 M (by omega)
          (appendBlockOrder hED small block) :=
      cyclicBasisOrder3_appendBlock_wrap M (by omega) hED small block
        hsmallM hD
        (by simpa [p, a, ip, ia] using h₁)
        (by simpa [a, ia] using h₂)
        (by simpa [b, ib] using h₃)
        (by simpa [b, c, ib, ic] using h₄)
    let order : Fin (m + 3) ≃ M.E :=
      (appendBlockOrder hED small block).trans (Equiv.setCongr hUnion)
    refine ⟨order, ?_⟩
    intro i
    have hi := hApp i
    simpa only [order, Equiv.trans_apply, Equiv.setCongr_apply] using hi
  · rcases hSecond with ⟨block, h₁, h₂, h₃, h₄⟩
    let rotated : Fin m ≃ (Matroid.delete M D).E :=
      rotateOneOrder (by omega) small
    have hrotSmall : CyclicBasisOrder3 M (by omega) rotated :=
      CyclicBasisOrder3.rotateOne M (by omega) small hsmallM

    have hrotPen :
        ((rotated ⟨m - 2, by omega⟩ : (Matroid.delete M D).E) : α) = a := by
      have hidx :
          cyclicIndex m (by omega) (⟨m - 2, by omega⟩ : Fin m) 1 = ia := by
        simpa [ip] using hip₁
      change ((rotateOneOrder (by omega) small
        (⟨m - 2, by omega⟩ : Fin m) : (Matroid.delete M D).E) : α) = a
      rw [rotateOneOrder_apply, hidx]
    have hrotLast :
        ((rotated ⟨m - 1, by omega⟩ : (Matroid.delete M D).E) : α) = b := by
      have hidx :
          cyclicIndex m (by omega) (⟨m - 1, by omega⟩ : Fin m) 1 = ib := by
        simpa [ia] using hia₁
      change ((rotateOneOrder (by omega) small
        (⟨m - 1, by omega⟩ : Fin m) : (Matroid.delete M D).E) : α) = b
      rw [rotateOneOrder_apply, hidx]
    have hrotZero :
        ((rotated ⟨0, by omega⟩ : (Matroid.delete M D).E) : α) = c := by
      have hidx :
          cyclicIndex m (by omega) (⟨0, by omega⟩ : Fin m) 1 = ic := by
        simpa [ib] using hib₁
      change ((rotateOneOrder (by omega) small
        (⟨0, by omega⟩ : Fin m) : (Matroid.delete M D).E) : α) = c
      rw [rotateOneOrder_apply, hidx]
    have hrotOne :
        ((rotated ⟨1, by omega⟩ : (Matroid.delete M D).E) : α) = q := by
      have hidx :
          cyclicIndex m (by omega) (⟨1, by omega⟩ : Fin m) 1 = iq := by
        apply Fin.ext
        change (1 + 1) % m = 2
        rw [Nat.mod_eq_of_lt (by omega)]
      change ((rotateOneOrder (by omega) small
        (⟨1, by omega⟩ : Fin m) : (Matroid.delete M D).E) : α) = q
      rw [rotateOneOrder_apply, hidx]

    have hApp :
        CyclicBasisOrder3 M (by omega)
          (appendBlockOrder hED rotated block) :=
      cyclicBasisOrder3_appendBlock_wrap M (by omega) hED rotated block
        hrotSmall hD
        (by
          rw [hrotPen, hrotLast]
          exact h₁)
        (by
          rw [hrotLast]
          exact h₂)
        (by
          rw [hrotZero]
          exact h₃)
        (by
          rw [hrotZero, hrotOne]
          exact h₄)
    let order : Fin (m + 3) ≃ M.E :=
      (appendBlockOrder hED rotated block).trans (Equiv.setCongr hUnion)
    refine ⟨order, ?_⟩
    intro i
    have hi := hApp i
    simpa only [order, Equiv.trans_apply, Equiv.setCongr_apply] using hi

#print axioms Rank3KUM.contiguousBasisSplicing

end

end Rank3KUM
