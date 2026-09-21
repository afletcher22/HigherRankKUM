import Rank3KUM.TwoGap.Ordering
import Rank3KUM.TwoGap.Support
import Mathlib.Tactic

namespace Rank3KUM.TwoGap

open Set

variable {α : Type*}

/-- Delete the final element of a displayed triple and insert a replacement. -/
theorem exchangeSet_triple_remove_third
    {x y z e : α}
    (hzx : z ≠ x) (hzy : z ≠ y) (hez : e ≠ z) :
    exchangeSet ({x, y, z} : Set α) z e =
      ({x, y, e} : Set α) := by
  ext t
  simp only [exchangeSet, Set.mem_sdiff, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  aesop

/-- Delete the first element of a displayed triple and insert a replacement. -/
theorem exchangeSet_triple_remove_first
    {x y z e : α}
    (hxy : x ≠ y) (hxz : x ≠ z) (hex : e ≠ x) :
    exchangeSet ({x, y, z} : Set α) x e =
      ({e, y, z} : Set α) := by
  ext t
  simp only [exchangeSet, Set.mem_sdiff, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  aesop

/-- Two unequal symmetric partners construct a valid first-gap ordering. -/
theorem firstGapWorks_of_distinct_symmetricPartners
    (M : Matroid α) {D : Set α} {p a b c u w : α}
    (hRank : M.eRank = 3)
    (hD : M.IsBase D)
    (haD : a ∉ D) (hbD : b ∉ D)
    (hpb : p ≠ b) (hab : a ≠ b)
    (hba : b ≠ a) (hca : c ≠ a)
    (hu : u ∈ SymmetricPartners M D ({p, a, b} : Set α) b)
    (hw : w ∈ SymmetricPartners M D ({a, b, c} : Set α) a)
    (huw : u ≠ w) :
    FirstGapWorks M D p a b c := by
  have hu' := (mem_symmetricPartners M D ({p, a, b} : Set α) b u).mp hu
  have hw' := (mem_symmetricPartners M D ({a, b, c} : Set α) a w).mp hw
  have hcard : D.encard = 3 :=
    hD.encard_eq_eRank.trans hRank
  obtain ⟨d, hd0, hd2⟩ :=
    exists_fin3_equiv_with_endpoints hcard hu'.1 hw'.1 huw
  have hDset0 := set_eq_triple_of_fin3_equiv d
  have hDset :
      D = ({u, (d 1 : α), w} : Set α) := by
    simpa [hd0, hd2] using hDset0
  have h01 : u ≠ (d 1 : α) := by
    intro h
    have hsub : d (0 : Fin 3) = d (1 : Fin 3) :=
      Subtype.ext (hd0.trans h)
    have hidx : (0 : Fin 3) = 1 := d.injective hsub
    omega
  have h21 : w ≠ (d 1 : α) := by
    intro h
    have hsub : d (2 : Fin 3) = d (1 : Fin 3) :=
      Subtype.ext (hd2.trans h)
    have hidx : (2 : Fin 3) = 1 := d.injective hsub
    omega
  have hub : u ≠ b := by
    intro h
    exact hu'.2.1 (by simp [h])
  have hwa : w ≠ a := by
    intro h
    exact hw'.2.1 (by simp [h])
  have hbu : b ≠ u := by
    intro h
    apply hbD
    rw [h]
    exact hu'.1
  have haw : a ≠ w := by
    intro h
    apply haD
    rw [h]
    exact hw'.1

  have h1 : M.IsBase ({p, a, u} : Set α) := by
    rw [← exchangeSet_triple_remove_third hpb.symm hba hub]
    exact hu'.2.2.2
  have h2 : M.IsBase ({a, u, (d 1 : α)} : Set α) := by
    have heq :
        exchangeSet D w a = ({u, (d 1 : α), a} : Set α) := by
      calc
        exchangeSet D w a =
            exchangeSet ({u, (d 1 : α), w} : Set α) w a :=
          congrArg (fun X : Set α => exchangeSet X w a) hDset
        _ = ({u, (d 1 : α), a} : Set α) :=
          exchangeSet_triple_remove_third huw.symm h21 haw
    have hbase : M.IsBase ({u, (d 1 : α), a} : Set α) := by
      rw [← heq]
      exact hw'.2.2.1
    have hset :
        ({u, (d 1 : α), a} : Set α) =
          ({a, u, (d 1 : α)} : Set α) := by
      ext t
      simp [or_comm, or_left_comm]
    rw [← hset]
    exact hbase
  have h3 : M.IsBase ({(d 1 : α), w, b} : Set α) := by
    have heq :
        exchangeSet D u b = ({b, (d 1 : α), w} : Set α) := by
      calc
        exchangeSet D u b =
            exchangeSet ({u, (d 1 : α), w} : Set α) u b :=
          congrArg (fun X : Set α => exchangeSet X u b) hDset
        _ = ({b, (d 1 : α), w} : Set α) :=
          exchangeSet_triple_remove_first h01 huw hbu
    have hbase : M.IsBase ({b, (d 1 : α), w} : Set α) := by
      rw [← heq]
      exact hu'.2.2.1
    have hset :
        ({b, (d 1 : α), w} : Set α) =
          ({(d 1 : α), w, b} : Set α) := by
      ext t
      simp [or_comm, or_assoc]
    rw [← hset]
    exact hbase
  have h4 : M.IsBase ({w, b, c} : Set α) := by
    rw [← exchangeSet_triple_remove_first hab hca.symm hwa]
    exact hw'.2.2.2

  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · simpa [hd0] using h1
  · simpa [hd0] using h2
  · simpa [hd2] using h3
  · simpa [hd2] using h4

/-- Two unequal symmetric partners construct a valid second-gap ordering. -/
theorem secondGapWorks_of_distinct_symmetricPartners
    (M : Matroid α) {D : Set α} {a b c q u w : α}
    (hRank : M.eRank = 3)
    (hD : M.IsBase D)
    (hbD : b ∉ D) (hcD : c ∉ D)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hcb : c ≠ b) (hqb : q ≠ b)
    (hu : u ∈ SymmetricPartners M D ({a, b, c} : Set α) c)
    (hw : w ∈ SymmetricPartners M D ({b, c, q} : Set α) b)
    (huw : u ≠ w) :
    SecondGapWorks M D a b c q := by
  have hu' := (mem_symmetricPartners M D ({a, b, c} : Set α) c u).mp hu
  have hw' := (mem_symmetricPartners M D ({b, c, q} : Set α) b w).mp hw
  have hcard : D.encard = 3 :=
    hD.encard_eq_eRank.trans hRank
  obtain ⟨d, hd0, hd2⟩ :=
    exists_fin3_equiv_with_endpoints hcard hu'.1 hw'.1 huw
  have hDset0 := set_eq_triple_of_fin3_equiv d
  have hDset :
      D = ({u, (d 1 : α), w} : Set α) := by
    simpa [hd0, hd2] using hDset0
  have h01 : u ≠ (d 1 : α) := by
    intro h
    have hsub : d (0 : Fin 3) = d (1 : Fin 3) :=
      Subtype.ext (hd0.trans h)
    have hidx : (0 : Fin 3) = 1 := d.injective hsub
    omega
  have h21 : w ≠ (d 1 : α) := by
    intro h
    have hsub : d (2 : Fin 3) = d (1 : Fin 3) :=
      Subtype.ext (hd2.trans h)
    have hidx : (2 : Fin 3) = 1 := d.injective hsub
    omega
  have huc : u ≠ c := by
    intro h
    exact hu'.2.1 (by simp [h])
  have hwb : w ≠ b := by
    intro h
    exact hw'.2.1 (by simp [h])
  have hcu : c ≠ u := by
    intro h
    apply hcD
    rw [h]
    exact hu'.1
  have hbw : b ≠ w := by
    intro h
    apply hbD
    rw [h]
    exact hw'.1

  have h1 : M.IsBase ({a, b, u} : Set α) := by
    rw [← exchangeSet_triple_remove_third hac.symm hcb huc]
    exact hu'.2.2.2
  have h2 : M.IsBase ({b, u, (d 1 : α)} : Set α) := by
    have heq :
        exchangeSet D w b = ({u, (d 1 : α), b} : Set α) := by
      calc
        exchangeSet D w b =
            exchangeSet ({u, (d 1 : α), w} : Set α) w b :=
          congrArg (fun X : Set α => exchangeSet X w b) hDset
        _ = ({u, (d 1 : α), b} : Set α) :=
          exchangeSet_triple_remove_third huw.symm h21 hbw
    have hbase : M.IsBase ({u, (d 1 : α), b} : Set α) := by
      rw [← heq]
      exact hw'.2.2.1
    have hset :
        ({u, (d 1 : α), b} : Set α) =
          ({b, u, (d 1 : α)} : Set α) := by
      ext t
      simp [or_comm, or_left_comm]
    rw [← hset]
    exact hbase
  have h3 : M.IsBase ({(d 1 : α), w, c} : Set α) := by
    have heq :
        exchangeSet D u c = ({c, (d 1 : α), w} : Set α) := by
      calc
        exchangeSet D u c =
            exchangeSet ({u, (d 1 : α), w} : Set α) u c :=
          congrArg (fun X : Set α => exchangeSet X u c) hDset
        _ = ({c, (d 1 : α), w} : Set α) :=
          exchangeSet_triple_remove_first h01 huw hcu
    have hbase : M.IsBase ({c, (d 1 : α), w} : Set α) := by
      rw [← heq]
      exact hu'.2.2.1
    have hset :
        ({c, (d 1 : α), w} : Set α) =
          ({(d 1 : α), w, c} : Set α) := by
      ext t
      simp [or_comm, or_assoc]
    rw [← hset]
    exact hbase
  have h4 : M.IsBase ({w, c, q} : Set α) := by
    rw [← exchangeSet_triple_remove_first hbc hqb.symm hwb]
    exact hw'.2.2.2

  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · simpa [hd0] using h1
  · simpa [hd0] using h2
  · simpa [hd2] using h3
  · simpa [hd2] using h4

/-- If the first gap does not work, its two partner sets are blocked. -/
theorem firstGapBlocked_of_not_works
    (M : Matroid α) {D : Set α} {p a b c : α}
    (hRank : M.eRank = 3) (hD : M.IsBase D)
    (haD : a ∉ D) (hbD : b ∉ D)
    (hpb : p ≠ b) (hab : a ≠ b)
    (hba : b ≠ a) (hca : c ≠ a)
    (hnot : ¬ FirstGapWorks M D p a b c) :
    GapBlocked
      (SymmetricPartners M D ({p, a, b} : Set α) b)
      (SymmetricPartners M D ({a, b, c} : Set α) a) := by
  rintro ⟨u, hu, w, hw, huw⟩
  exact hnot <|
    firstGapWorks_of_distinct_symmetricPartners M hRank hD haD hbD
      hpb hab hba hca hu hw huw

/-- If the second gap does not work, its two partner sets are blocked. -/
theorem secondGapBlocked_of_not_works
    (M : Matroid α) {D : Set α} {a b c q : α}
    (hRank : M.eRank = 3) (hD : M.IsBase D)
    (hbD : b ∉ D) (hcD : c ∉ D)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hcb : c ≠ b) (hqb : q ≠ b)
    (hnot : ¬ SecondGapWorks M D a b c q) :
    GapBlocked
      (SymmetricPartners M D ({a, b, c} : Set α) c)
      (SymmetricPartners M D ({b, c, q} : Set α) b) := by
  rintro ⟨u, hu, w, hw, huw⟩
  exact hnot <|
    secondGapWorks_of_distinct_symmetricPartners M hRank hD hbD hcD
      hac hbc hcb hqb hu hw huw

end Rank3KUM.TwoGap
