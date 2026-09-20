import Rank3KUM.Version2.SixPointPasch

namespace Rank3KUM.Version2

open Finset

/-- Six cyclic windows for the displayed order `(a,b,c,d,e,f)`. -/
def AvoidingCycle6
    (F : Finset (Finset (Fin 6)))
    (a b c d e f : Fin 6) : Prop :=
  ({a, b, c} : Finset (Fin 6)) ∉ F ∧
  ({b, c, d} : Finset (Fin 6)) ∉ F ∧
  ({c, d, e} : Finset (Fin 6)) ∉ F ∧
  ({d, e, f} : Finset (Fin 6)) ∉ F ∧
  ({e, f, a} : Finset (Fin 6)) ∉ F ∧
  ({f, a, b} : Finset (Fin 6)) ∉ F

/-- Six displayed elements have pairwise distinct entries when their finset has cardinality six. -/
theorem six_pairwise_ne_of_card_six
    {β : Type*} [DecidableEq β]
    {a b c d e f : β}
    (hcard : ({a, b, c, d, e, f} : Finset β).card = 6) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧
    b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧
    c ≠ d ∧ c ≠ e ∧ c ≠ f ∧
    d ≠ e ∧ d ≠ f ∧ e ≠ f := by
  have hn : ({a, b, c, d, e, f} : Multiset β).Nodup := by
    rw [← Multiset.toFinset_card_eq_card_iff_nodup]
    simpa using hcard
  have ha := (Multiset.nodup_cons.mp hn).1
  have hn1 := (Multiset.nodup_cons.mp hn).2
  have hb := (Multiset.nodup_cons.mp hn1).1
  have hn2 := (Multiset.nodup_cons.mp hn1).2
  have hc := (Multiset.nodup_cons.mp hn2).1
  have hn3 := (Multiset.nodup_cons.mp hn2).2
  have hd := (Multiset.nodup_cons.mp hn3).1
  have hn4 := (Multiset.nodup_cons.mp hn3).2
  have he := (Multiset.nodup_cons.mp hn4).1
  have hab : a ≠ b := by intro h; subst b; exact ha (by simp)
  have hac : a ≠ c := by intro h; subst c; exact ha (by simp)
  have had : a ≠ d := by intro h; subst d; exact ha (by simp)
  have hae : a ≠ e := by intro h; subst e; exact ha (by simp)
  have haf : a ≠ f := by intro h; subst f; exact ha (by simp)
  have hbc : b ≠ c := by intro h; subst c; exact hb (by simp)
  have hbd : b ≠ d := by intro h; subst d; exact hb (by simp)
  have hbe : b ≠ e := by intro h; subst e; exact hb (by simp)
  have hbf : b ≠ f := by intro h; subst f; exact hb (by simp)
  have hcd : c ≠ d := by intro h; subst d; exact hc (by simp)
  have hce : c ≠ e := by intro h; subst e; exact hc (by simp)
  have hcf : c ≠ f := by intro h; subst f; exact hc (by simp)
  have hde : d ≠ e := by intro h; subst e; exact hd (by simp)
  have hdf : d ≠ f := by intro h; subst f; exact hd (by simp)
  have hef : e ≠ f := by intro h; subst f; exact he (by simp)
  exact ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf,
    hcd, hce, hcf, hde, hdf, hef⟩

/-- Avoidance is inherited by subfamilies. -/
theorem avoidingCycle6_mono
    {F G : Finset (Finset (Fin 6))}
    (hFG : F ⊆ G)
    {a b c d e f : Fin 6}
    (h : AvoidingCycle6 G a b c d e f) :
    AvoidingCycle6 F a b c d e f := by
  unfold AvoidingCycle6 at h ⊢
  rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  exact ⟨fun hF => h0 (hFG hF),
    fun hF => h1 (hFG hF),
    fun hF => h2 (hFG hF),
    fun hF => h3 (hFG hF),
    fun hF => h4 (hFG hF),
    fun hF => h5 (hFG hF)⟩

/-- The first canonical family is avoided by the paper's cycle `(0,1,3,2,4,5)`. -/
theorem pairPattern6_has_paper_avoidingCycle
    {F : Finset (Finset (Fin 6))}
    (hPair : PairPattern6 F) :
    ∃ a b c d e f : Fin 6,
      ({a, b, c, d, e, f} : Finset (Fin 6)).card = 6 ∧
      AvoidingCycle6 F a b d c e f := by
  classical
  rcases hPair with ⟨a, b, c, d, e, f, hSix, hF⟩
  obtain ⟨hab, hac, had, hae, haf,
      hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    six_pairwise_ne_of_card_six hSix
  let A : Finset (Fin 6) := {a, b, c}
  let B : Finset (Fin 6) := {d, e, f}
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.2
    intro x hxA hxB
    simp only [A, B, Finset.mem_insert, Finset.mem_singleton] at hxA hxB
    rcases hxA with rfl | rfl | rfl <;>
      rcases hxB with rfl | rfl | rfl <;> contradiction
  have hMixed
      (W : Finset (Fin 6))
      {x y : Fin 6}
      (hxW : x ∈ W) (hxA : x ∈ A)
      (hyW : y ∈ W) (hyB : y ∈ B) :
      W ∉ ({A, B} : Finset (Finset (Fin 6))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro hWA
      have hyA : y ∈ A := by rw [← hWA]; exact hyW
      exact Finset.disjoint_left.mp hdisj hyA hyB
    · intro hWB
      have hxB : x ∈ B := by rw [← hWB]; exact hxW
      exact Finset.disjoint_left.mp hdisj hxA hxB
  refine ⟨a, b, c, d, e, f, hSix, ?_⟩
  unfold AvoidingCycle6
  rw [hF]
  change
    ({a, b, d} : Finset (Fin 6)) ∉ {A, B} ∧
    ({b, d, c} : Finset (Fin 6)) ∉ {A, B} ∧
    ({d, c, e} : Finset (Fin 6)) ∉ {A, B} ∧
    ({c, e, f} : Finset (Fin 6)) ∉ {A, B} ∧
    ({e, f, a} : Finset (Fin 6)) ∉ {A, B} ∧
    ({f, a, b} : Finset (Fin 6)) ∉ {A, B}
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hMixed _ (x := a) (y := d) (by simp) (by simp [A]) (by simp) (by simp [B])
  · exact hMixed _ (x := b) (y := d) (by simp) (by simp [A]) (by simp) (by simp [B])
  · exact hMixed _ (x := c) (y := d) (by simp) (by simp [A]) (by simp) (by simp [B])
  · exact hMixed _ (x := c) (y := e) (by simp) (by simp [A]) (by simp) (by simp [B])
  · exact hMixed _ (x := a) (y := e) (by simp) (by simp [A]) (by simp) (by simp [B])
  · exact hMixed _ (x := a) (y := f) (by simp) (by simp [A]) (by simp) (by simp [B])

/-- The Pasch family is avoided by the paper's cycle `(0,1,4,2,3,5)`. -/
theorem paschPattern6_has_paper_avoidingCycle
    {F : Finset (Finset (Fin 6))}
    (hPasch : PaschPattern6 F) :
    ∃ a b c d e f : Fin 6,
      ({a, b, c, d, e, f} : Finset (Fin 6)).card = 6 ∧
      AvoidingCycle6 F a b e c d f := by
  classical
  rcases hPasch with ⟨a, b, c, d, e, f, hSix, hF⟩
  obtain ⟨hab, hac, had, hae, haf,
      hbc, hbd, hbe, hbf,
      hcd, hce, hcf, hde, hdf, hef⟩ :=
    six_pairwise_ne_of_card_six hSix
  let A : Finset (Fin 6) := {a, b, c}
  let B : Finset (Fin 6) := {a, d, e}
  let C : Finset (Fin 6) := {b, d, f}
  let D : Finset (Fin 6) := {c, e, f}
  have hNeOfMemNotMem
      (W T : Finset (Fin 6)) {x : Fin 6}
      (hxW : x ∈ W) (hxT : x ∉ T) : W ≠ T := by
    intro hWT
    apply hxT
    rw [← hWT]
    exact hxW
  have heA : e ∉ A := by
    simp only [A, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hae.symm, hbe.symm, hce.symm⟩
  have hbB : b ∉ B := by
    simp only [B, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab.symm, hbd, hbe⟩
  have haC : a ∉ C := by
    simp only [C, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab, had, haf⟩
  have haD : a ∉ D := by
    simp only [D, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hac, hae, haf⟩
  have heC : e ∉ C := by
    simp only [C, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hbe.symm, hde.symm, hef⟩
  have hbD : b ∉ D := by
    simp only [D, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hbc, hbe, hbf⟩
  have hcB : c ∉ B := by
    simp only [B, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hac.symm, hcd, hce⟩
  have hcC : c ∉ C := by
    simp only [C, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hbc.symm, hcd, hcf⟩
  have hdD : d ∉ D := by
    simp only [D, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hcd.symm, hde, hdf⟩
  have hfA : f ∉ A := by
    simp only [A, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨haf.symm, hbf.symm, hcf.symm⟩
  have hfB : f ∉ B := by
    simp only [B, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨haf.symm, hdf.symm, hef.symm⟩
  refine ⟨a, b, c, d, e, f, hSix, ?_⟩
  unfold AvoidingCycle6
  rw [hF]
  change
    ({a, b, e} : Finset (Fin 6)) ∉ {A, B, C, D} ∧
    ({b, e, c} : Finset (Fin 6)) ∉ {A, B, C, D} ∧
    ({e, c, d} : Finset (Fin 6)) ∉ {A, B, C, D} ∧
    ({c, d, f} : Finset (Fin 6)) ∉ {A, B, C, D} ∧
    ({d, f, a} : Finset (Fin 6)) ∉ {A, B, C, D} ∧
    ({f, a, b} : Finset (Fin 6)) ∉ {A, B, C, D}
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨
      hNeOfMemNotMem _ A (by simp) heA,
      hNeOfMemNotMem _ B (by simp) hbB,
      hNeOfMemNotMem _ C (by simp) haC,
      hNeOfMemNotMem _ D (by simp) haD⟩
  · exact ⟨
      hNeOfMemNotMem _ A (by simp) heA,
      hNeOfMemNotMem _ B (by simp) hbB,
      hNeOfMemNotMem _ C (by simp) heC,
      hNeOfMemNotMem _ D (by simp) hbD⟩
  · exact ⟨
      hNeOfMemNotMem _ A (by simp) heA,
      hNeOfMemNotMem _ B (by simp) hcB,
      hNeOfMemNotMem _ C (by simp) hcC,
      hNeOfMemNotMem _ D (by simp) hdD⟩
  · exact ⟨
      hNeOfMemNotMem _ A (by simp) hfA,
      hNeOfMemNotMem _ B (by simp) hcB,
      hNeOfMemNotMem _ C (by simp) hcC,
      hNeOfMemNotMem _ D (by simp) hdD⟩
  · exact ⟨
      hNeOfMemNotMem _ A (by simp) hfA,
      hNeOfMemNotMem _ B (by simp) hfB,
      hNeOfMemNotMem _ C (by simp) haC,
      hNeOfMemNotMem _ D (by simp) haD⟩
  · exact ⟨
      hNeOfMemNotMem _ A (by simp) hfA,
      hNeOfMemNotMem _ B (by simp) hfB,
      hNeOfMemNotMem _ C (by simp) haC,
      hNeOfMemNotMem _ D (by simp) haD⟩

/-- Classification of inclusion-maximal linear triple families on six points. -/
theorem maximalLinearTripleFamily6_pair_or_pasch
    {F : Finset (Finset (Fin 6))}
    (hMax : MaximalLinearTripleFamily6 F) :
    PairPattern6 F ∨ PaschPattern6 F := by
  by_cases hInt : PairwiseIntersecting6 F
  · exact Or.inr (paschPattern6_of_maximal_pairwiseIntersecting hMax hInt)
  · left
    unfold PairwiseIntersecting6 at hInt
    push Not at hInt
    obtain ⟨A, hAF, B, hBF, hAB, hdisj⟩ := hInt
    exact pairPattern6_of_disjoint_members hMax.1 hAF hBF hAB hdisj

/-- Every linear family has a maximal extension of one of the two canonical types. -/
theorem exists_maximal_pair_or_pasch_superset
    {F : Finset (Finset (Fin 6))}
    (hF : LinearTripleFamily6 F) :
    ∃ G : Finset (Finset (Fin 6)),
      F ⊆ G ∧ (PairPattern6 G ∨ PaschPattern6 G) := by
  obtain ⟨G, hFG, hMax⟩ := exists_maximalLinearTripleFamily6_superset F hF
  exact ⟨G, hFG, maximalLinearTripleFamily6_pair_or_pasch hMax⟩

/--
Paper v2, Lemma 9.2. Every linear family of triples on six points admits a
cyclic order whose six three-element windows avoid the family.
-/
theorem exists_avoidingCycle6_of_linear
    {F : Finset (Finset (Fin 6))}
    (hF : LinearTripleFamily6 F) :
    ∃ a b c d e f : Fin 6,
      ({a, b, c, d, e, f} : Finset (Fin 6)).card = 6 ∧
      AvoidingCycle6 F a b c d e f := by
  obtain ⟨G, hFG, hPair | hPasch⟩ := exists_maximal_pair_or_pasch_superset hF
  · obtain ⟨a, b, c, d, e, f, hSix, hAvoid⟩ :=
      pairPattern6_has_paper_avoidingCycle hPair
    refine ⟨a, b, d, c, e, f, ?_, avoidingCycle6_mono hFG hAvoid⟩
    have hset :
        ({a, b, d, c, e, f} : Finset (Fin 6)) =
          ({a, b, c, d, e, f} : Finset (Fin 6)) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hset, hSix]
  · obtain ⟨a, b, c, d, e, f, hSix, hAvoid⟩ :=
      paschPattern6_has_paper_avoidingCycle hPasch
    refine ⟨a, b, e, c, d, f, ?_, avoidingCycle6_mono hFG hAvoid⟩
    have hset :
        ({a, b, e, c, d, f} : Finset (Fin 6)) =
          ({a, b, c, d, e, f} : Finset (Fin 6)) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hset, hSix]

end Rank3KUM.Version2
