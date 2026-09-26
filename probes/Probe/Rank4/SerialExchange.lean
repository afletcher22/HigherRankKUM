import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# Serial symmetric exchanges in rank 4 (Kotlar–Ziv)

D. Kotlar and R. Ziv, *On serial symmetric exchanges of matroid bases*, J. Graph Theory (2012),
arXiv:1110.1826. Theorem 4.2 of arXiv v3: two disjoint bases `A`, `B` of a rank-4 matroid have
a full serial symmetric exchange. There are orderings `A = {p₁, p₂, p₃, p₄}` and
`B = {q₁, q₂, q₃, q₄}` such that for every `i` both `(A - {p₁ … pᵢ}) + {q₁ … qᵢ}` and
`(B - {q₁ … qᵢ}) + {p₁ … pᵢ}` are bases (`serial_exchange_rank_four`). Equivalently, the cyclic
sequence `p₁ p₂ p₃ p₄ q₁ q₂ q₃ q₄` has all eight 4-windows bases (`cyclic_windows_rank_four`).

## Proof structure (paper numbering)

* Observation 2.3, symmetric exchange (`exists_symm_exchange`), and Proposition 2.8, that
  `Conn(x, y, P, Q)` is never a singleton (`exists_other_conn`). Both follow from one fact
  (`exists_ne_notMem_closure_of_isCircuit`): a circuit that has an element outside a flat has a
  second one. It is applied to the fundamental circuit of `x` in `Q` and the flat `cl(P - y)`,
  which is the circuit–cocircuit argument of the paper.
* Theorem 3.3: every pair `{a₁, a₂} ⊆ A` has a serial symmetric exchange with some pair of `B`
  (`exists_serialPair`). The early exit is `serialPair_of_second`. The elements `b₂`, `b₃` of
  (3.1)–(3.3) are found in `kz_witnesses`. The final bases (3.5) and (3.6) come from `kz_final_left`
  and `kz_right`, and the two cases are assembled in `serialPair_of_witnesses`.
* Proposition 4.1 (`fullSerial_of_serialPair`) and Theorem 4.2 (`serial_exchange_rank_four`).

## Deviations from the paper

The paper argues with fundamental circuits, circuit elimination (Lemma 2.6) and Lemmas 2.9–2.11.
Here each such step is replaced by a closure argument that uses only

* `isBase_insert_sdiff_iff`: `P - p + e` is a basis iff `e ∉ cl(P - p)`, and
* `mem_closure_sdiff_sdiff`: for independent `I`, `cl(I - p) ∩ cl(I - q) ⊆ cl(I - p - q)`.

The two final bases `A - {a₁, a₂} + {b₂, b₃}` and `B - {b₂, b₃} + {a₁, a₂}` of Theorem 3.3 are
the same in both cases of the paper. They are proved once, before the case split, and (3.4) is
not needed for them. In Case 2 the paper passes to `A'' = A - a₂ + b₁` and re-runs Case 1. Here
we show directly that `(a₂, b₂)` is a symmetric exchange for `A` and `B`. That is the pair the
paper's re-run produces (`A** = A - a₂ + b₂`, `B** = B - b₂ + a₂`).
-/

namespace HigherRankKUM.KotlarZiv

open Set

variable {α : Type*} {M : Matroid α}

/-! ### Single exchanges and closures -/

/-- Replacing `p` by an outside element `e` in a basis `P` gives a basis exactly when `e` is not
spanned by `P - p`. -/
theorem isBase_insert_sdiff_iff {P : Set α} {p e : α} (hP : M.IsBase P) (heE : e ∈ M.E)
    (heP : e ∉ P) : M.IsBase (insert e (P \ {p})) ↔ e ∉ M.closure (P \ {p}) := by
  have hI : M.Indep (P \ {p}) := hP.indep.subset Set.sdiff_subset
  have he : e ∉ P \ {p} := fun h => heP h.1
  constructor
  · intro h
    exact ((hI.insert_indep_iff_of_notMem he).1 h.indep).2
  · intro h
    exact hP.exchange_isBase_of_indep heP ((hI.insert_indep_iff_of_notMem he).2 ⟨heE, h⟩)

/-- A failed exchange means that `e` is spanned by `P - p`. -/
theorem mem_closure_of_not_isBase {P : Set α} {p e : α} (hP : M.IsBase P) (heE : e ∈ M.E)
    (heP : e ∉ P) (h : ¬ M.IsBase (insert e (P \ {p}))) : e ∈ M.closure (P \ {p}) := by
  by_contra hc
  exact h ((isBase_insert_sdiff_iff hP heE heP).2 hc)

/-- A successful exchange means that `e` is not spanned by `P - p`. -/
theorem notMem_closure_of_isBase {P : Set α} {p e : α} (hP : M.IsBase P) (heE : e ∈ M.E)
    (heP : e ∉ P) (h : M.IsBase (insert e (P \ {p}))) : e ∉ M.closure (P \ {p}) :=
  (isBase_insert_sdiff_iff hP heE heP).1 h

/-- For an independent set `I`, an element spanned by both `I - p` and `I - q` is spanned by
`I - p - q`. -/
theorem mem_closure_sdiff_sdiff {I : Set α} {p q e : α} (hI : M.Indep I)
    (h₁ : e ∈ M.closure (I \ {p})) (h₂ : e ∈ M.closure (I \ {q})) :
    e ∈ M.closure (I \ {p} \ {q}) := by
  have hU : M.Indep ((I \ {p}) ∪ (I \ {q})) :=
    hI.subset (Set.union_subset Set.sdiff_subset Set.sdiff_subset)
  have h : e ∈ M.closure ((I \ {p}) ∩ (I \ {q})) := by
    rw [hU.closure_inter_eq_inter_closure]
    exact ⟨h₁, h₂⟩
  have hsub : (I \ {p}) ∩ (I \ {q}) ⊆ I \ {p} \ {q} := fun x hx => ⟨hx.1, hx.2.2⟩
  exact M.closure_subset_closure hsub h

/-- If `u` is spanned by `P - x` but not by `P - x - y`, then `P - y + u` is a basis. -/
theorem isBase_insert_of_closure {P : Set α} {x y u : α} (hP : M.IsBase P) (huE : u ∈ M.E)
    (huP : u ∉ P) (h₁ : u ∈ M.closure (P \ {x})) (h₂ : u ∉ M.closure (P \ {x} \ {y})) :
    M.IsBase (insert u (P \ {y})) :=
  (isBase_insert_sdiff_iff hP huE huP).2 fun h => h₂ (mem_closure_sdiff_sdiff hP.indep h₁ h)

/-- If `P - p` lies in the closure of `S` and `e` does not, then `P - p + e` is a basis. -/
theorem isBase_insert_of_subset_closure {P S : Set α} {p e : α} (hP : M.IsBase P) (hp : p ∈ P)
    (hPS : P \ {p} ⊆ M.closure S) (heE : e ∈ M.E) (heS : e ∉ M.closure S) :
    M.IsBase (insert e (P \ {p})) := by
  have he : e ∉ M.closure (P \ {p}) :=
    fun h => heS (M.closure_subset_closure_of_subset_closure hPS h)
  by_cases heP : e ∈ P
  · by_cases hep : e = p
    · rw [hep, Set.insert_sdiff_self_of_mem hp]
      exact hP
    · exact absurd (M.mem_closure_of_mem' ⟨heP, hep⟩ heE) he
  · exact (isBase_insert_sdiff_iff hP heE heP).2 he

/-! ### Fundamental circuits: Observation 2.3 and Proposition 2.8 -/

/-- If a circuit has an element outside the closure of `X`, it has a second one. -/
theorem exists_ne_notMem_closure_of_isCircuit {C X : Set α} {e : α} (hC : M.IsCircuit C)
    (heC : e ∈ C) (heX : e ∉ M.closure X) : ∃ f ∈ C, f ≠ e ∧ f ∉ M.closure X := by
  by_contra hcon
  have hsub : C \ {e} ⊆ M.closure X := by
    intro f hf
    by_contra hfX
    exact hcon ⟨f, hf.1, hf.2, hfX⟩
  exact heX (M.closure_subset_closure_of_subset_closure hsub
    (hC.mem_closure_sdiff_singleton_of_mem heC))

/-- An element `f ∈ Q` of the fundamental circuit of `x ∉ Q` in the basis `Q` can be exchanged
for `x`. -/
theorem isBase_of_mem_fundCircuit {Q : Set α} {x f : α} (hQ : M.IsBase Q) (hxE : x ∈ M.E)
    (hxQ : x ∉ Q) (hfQ : f ∈ Q) (hf : f ∈ M.fundCircuit x Q) :
    M.IsBase (insert x (Q \ {f})) := by
  have hxf : x ≠ f := fun h => hxQ (by rw [h]; exact hfQ)
  have hI := (hQ.indep.mem_fundCircuit_iff (by rw [hQ.closure_eq]; exact hxE) hxQ).1 hf
  rw [Set.insert_sdiff_singleton_comm hxf]
  exact hQ.exchange_isBase_of_indep' hfQ hxQ hI

/-- Conversely, an element `f ∈ Q` that can be exchanged for `x` lies in the fundamental circuit
of `x`. -/
theorem mem_fundCircuit_of_isBase {Q : Set α} {x f : α} (hQ : M.IsBase Q) (hxE : x ∈ M.E)
    (hxQ : x ∉ Q) (hfQ : f ∈ Q) (h : M.IsBase (insert x (Q \ {f}))) :
    f ∈ M.fundCircuit x Q := by
  have hxf : x ≠ f := fun h => hxQ (by rw [h]; exact hfQ)
  rw [hQ.indep.mem_fundCircuit_iff (by rw [hQ.closure_eq]; exact hxE) hxQ,
    ← Set.insert_sdiff_singleton_comm hxf]
  exact h.indep

/-- Let `e` lie in the fundamental circuit of `x` in the basis `Q`, outside `cl X`. If `x = e`
or `x ∈ cl X`, some other element `f ∈ Q` of that circuit lies outside `cl X`, and
`Q - f + x` is a basis. -/
theorem exists_exchange_notMem_closure {Q X : Set α} {x e : α} (hQ : M.IsBase Q)
    (hxE : x ∈ M.E) (hxQ : x ∉ Q) (he : e ∈ M.fundCircuit x Q) (heX : e ∉ M.closure X)
    (hx : x = e ∨ x ∈ M.closure X) :
    ∃ f ∈ Q, f ≠ e ∧ f ∉ M.closure X ∧ M.IsBase (insert x (Q \ {f})) := by
  have hC := hQ.fundCircuit_isCircuit hxE hxQ
  obtain ⟨f, hfC, hfe, hfX⟩ := exists_ne_notMem_closure_of_isCircuit hC he heX
  have hfx : f ≠ x := by
    intro h
    rcases hx with hx | hx
    · exact hfe (h.trans hx)
    · exact hfX (by rw [h]; exact hx)
  have hfQ : f ∈ Q := by
    rcases Set.mem_insert_iff.1 (M.fundCircuit_subset_insert x Q hfC) with h | h
    · exact absurd h hfx
    · exact h
  exact ⟨f, hfQ, hfe, hfX, isBase_of_mem_fundCircuit hQ hxE hxQ hfQ hfC⟩

/-- **Observation 2.3.** Every `a ∈ P` has a symmetric exchange partner `b ∈ Q`. -/
theorem exists_symm_exchange {P Q : Set α} {a : α} (hP : M.IsBase P) (hQ : M.IsBase Q)
    (hPQ : Disjoint P Q) (ha : a ∈ P) :
    ∃ b ∈ Q, M.IsBase (insert b (P \ {a})) ∧ M.IsBase (insert a (Q \ {b})) := by
  have haE : a ∈ M.E := hP.subset_ground ha
  have haQ : a ∉ Q := Set.disjoint_left.1 hPQ ha
  have haX : a ∉ M.closure (P \ {a}) := hP.indep.notMem_closure_sdiff_of_mem ha
  obtain ⟨f, hfQ, -, hfX, hbase⟩ :=
    exists_exchange_notMem_closure hQ haE haQ (M.mem_fundCircuit a Q) haX (Or.inl rfl)
  have hfP : f ∉ P := Set.disjoint_right.1 hPQ hfQ
  exact ⟨f, hfQ, (isBase_insert_sdiff_iff hP (hQ.subset_ground hfQ) hfP).2 hfX, hbase⟩

/-- **Proposition 2.8.** For `x ≠ y` in `P`, the set
`Conn(x, y, P, Q) = {b ∈ Q | Q - b + x and P - y + b are bases}` is never a singleton. -/
theorem exists_other_conn {P Q : Set α} {x y b₀ : α} (hP : M.IsBase P) (hQ : M.IsBase Q)
    (hPQ : Disjoint P Q) (hx : x ∈ P) (hxy : x ≠ y) (hb₀ : b₀ ∈ Q)
    (h₁ : M.IsBase (insert x (Q \ {b₀}))) (h₂ : M.IsBase (insert b₀ (P \ {y}))) :
    ∃ b ∈ Q, b ≠ b₀ ∧ M.IsBase (insert x (Q \ {b})) ∧ M.IsBase (insert b (P \ {y})) := by
  have hxE : x ∈ M.E := hP.subset_ground hx
  have hxQ : x ∉ Q := Set.disjoint_left.1 hPQ hx
  have hb₀P : b₀ ∉ P := Set.disjoint_right.1 hPQ hb₀
  have hb₀C : b₀ ∈ M.fundCircuit x Q := mem_fundCircuit_of_isBase hQ hxE hxQ hb₀ h₁
  have hb₀X : b₀ ∉ M.closure (P \ {y}) :=
    notMem_closure_of_isBase hP (hQ.subset_ground hb₀) hb₀P h₂
  have hxX : x ∈ M.closure (P \ {y}) := M.mem_closure_of_mem' ⟨hx, hxy⟩ hxE
  obtain ⟨f, hfQ, hfb₀, hfX, hbase⟩ :=
    exists_exchange_notMem_closure hQ hxE hxQ hb₀C hb₀X (Or.inr hxX)
  have hfP : f ∉ P := Set.disjoint_right.1 hPQ hfQ
  exact ⟨f, hfQ, hfb₀, hbase, (isBase_insert_sdiff_iff hP (hQ.subset_ground hfQ) hfP).2 hfX⟩

/-- A symmetric exchange of disjoint sets leaves them disjoint. -/
theorem disjoint_exchange {A B : Set α} {a b : α} (hAB : Disjoint A B) (ha : a ∈ A)
    (hb : b ∈ B) : Disjoint (insert b (A \ {a})) (insert a (B \ {b})) := by
  rw [Set.disjoint_left]
  rintro x (hxb | ⟨hxA, hxa⟩) (hxa' | ⟨hxB, hxb'⟩)
  · exact Set.disjoint_left.1 hAB ha (by rw [← hxa', hxb]; exact hb)
  · exact hxb' hxb
  · exact hxa hxa'
  · exact Set.disjoint_left.1 hAB hxA hxB

/-! ### Theorem 3.3: serial symmetric exchanges of pairs -/

/-- `(x₁, y₁), (x₂, y₂)` is a serial symmetric exchange of the bases `A` and `B`
(Definition 2.1(ii) with `k = 2`). -/
structure SerialPair (M : Matroid α) (A B : Set α) (x₁ x₂ y₁ y₂ : α) : Prop where
  base₁ : M.IsBase (insert y₁ (A \ {x₁}))
  base₁' : M.IsBase (insert x₁ (B \ {y₁}))
  base₂ : M.IsBase (insert y₁ (insert y₂ (A \ {x₁} \ {x₂})))
  base₂' : M.IsBase (insert x₁ (insert x₂ (B \ {y₁} \ {y₂})))

/-- The early exit of Theorem 3.3: after exchanging `(a₁, b₁)`, `a₂` has a symmetric exchange
partner `b`. -/
theorem serialPair_of_second {A B : Set α} {a₁ a₂ b₁ b : α} (hAB : Disjoint A B)
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∈ B) (hb : b ∈ B)
    (h₁ : M.IsBase (insert b₁ (A \ {a₁}))) (h₂ : M.IsBase (insert a₁ (B \ {b₁})))
    (h₃ : M.IsBase (insert b (insert b₁ (A \ {a₁}) \ {a₂})))
    (h₄ : M.IsBase (insert a₂ (insert a₁ (B \ {b₁}) \ {b}))) :
    SerialPair M A B a₁ a₂ b₁ b := by
  have hb₁a₂ : b₁ ≠ a₂ := fun h => Set.disjoint_left.1 hAB ha₂ (by rw [← h]; exact hb₁)
  have ha₁b : a₁ ≠ b := fun h => Set.disjoint_left.1 hAB ha₁ (by rw [h]; exact hb)
  refine ⟨h₁, h₂, ?_, ?_⟩
  · rw [← Set.insert_sdiff_singleton_comm hb₁a₂, Set.insert_comm] at h₃
    exact h₃
  · rw [← Set.insert_sdiff_singleton_comm ha₁b, Set.insert_comm] at h₄
    exact h₄

/-- Equations (3.1)–(3.3). Here `P = A'` and `Q = B'` are the bases after the first exchange
`(a₁, b₁)`, and `a₂` is symmetrically exchangeable only with `a₁`. -/
theorem kz_witnesses {P Q : Set α} {a₁ a₂ b₁ : α} (hP : M.IsBase P) (hQ : M.IsBase Q)
    (hPQ : Disjoint P Q) (ha₂ : a₂ ∈ P) (hb₁ : b₁ ∈ P) (hab : a₂ ≠ b₁) (ha₁ : a₁ ∈ Q)
    (hB : M.IsBase (insert b₁ (Q \ {a₁}))) (hA : M.IsBase (insert a₁ (P \ {b₁})))
    (h4a : M.IsBase (insert a₁ (P \ {a₂}))) (h4b : M.IsBase (insert a₂ (Q \ {a₁})))
    (hno : ∀ b ∈ Q, b ≠ a₁ → M.IsBase (insert b (P \ {a₂})) →
      ¬ M.IsBase (insert a₂ (Q \ {b}))) :
    ∃ b₂ ∈ Q, ∃ b₃ ∈ Q, b₂ ≠ a₁ ∧ b₃ ≠ a₁ ∧ b₂ ≠ b₃ ∧
      M.IsBase (insert b₁ (Q \ {b₂})) ∧ M.IsBase (insert b₂ (P \ {a₂})) ∧
      M.IsBase (insert a₂ (Q \ {b₃})) ∧ M.IsBase (insert b₃ (P \ {b₁})) ∧
      ¬ M.IsBase (insert a₂ (Q \ {b₂})) ∧ ¬ M.IsBase (insert b₃ (P \ {a₂})) := by
  -- (3.1): `a₁ ∈ Conn(b₁, a₂, A', B')`, so there is a second element `b₂`
  obtain ⟨b₂, hb₂, hb₂a, h31a, h31b⟩ := exists_other_conn hP hQ hPQ hb₁ hab.symm ha₁ hB h4a
  -- (3.2): `a₁ ∈ Conn(a₂, b₁, A', B')`, so there is a second element `b₃`
  obtain ⟨b₃, hb₃, hb₃a, h32a, h32b⟩ := exists_other_conn hP hQ hPQ ha₂ hab ha₁ h4b hA
  -- (3.3)
  have h33a := hno b₂ hb₂ hb₂a h31b
  have h33b : ¬ M.IsBase (insert b₃ (P \ {a₂})) := fun h => hno b₃ hb₃ hb₃a h h32a
  have h23 : b₂ ≠ b₃ := by
    intro h
    rw [h] at h33a
    exact h33a h32a
  exact ⟨b₂, hb₂, b₃, hb₃, hb₂a, hb₃a, h23, h31a, h31b, h32a, h32b, h33a, h33b⟩

/-- Equation (3.5): `P - y - x + v + u` is a basis. In the application `P = A'`, `x = a₂`,
`y = b₁`, `u = b₂` and `v = b₃`. -/
theorem kz_final_left {P : Set α} {x y u v : α} (hP : M.IsBase P) (hx : x ∈ P) (hxy : x ≠ y)
    (huE : u ∈ M.E) (huP : u ∉ P) (hvE : v ∈ M.E) (hvP : v ∉ P)
    (h₁ : M.IsBase (insert u (P \ {x}))) (h₂ : M.IsBase (insert v (P \ {y})))
    (h₃ : ¬ M.IsBase (insert v (P \ {x}))) :
    M.IsBase (insert u (insert v (P \ {y} \ {x}))) := by
  have hvx : v ≠ x := fun h => hvP (by rw [h]; exact hx)
  have hv : v ∈ M.closure (P \ {x}) := mem_closure_of_not_isBase hP hvE hvP h₃
  have hu : u ∉ M.closure (P \ {x}) := notMem_closure_of_isBase hP huE huP h₁
  have hsub : insert v (P \ {y}) \ {x} ⊆ M.closure (P \ {x}) := by
    rintro w ⟨hw, hwx⟩
    rcases Set.mem_insert_iff.1 hw with hwv | ⟨hwP, -⟩
    · rw [hwv]
      exact hv
    · exact M.mem_closure_of_mem' ⟨hwP, hwx⟩ (hP.subset_ground hwP)
  have h := isBase_insert_of_subset_closure h₂ (Set.mem_insert_of_mem v ⟨hx, hxy⟩) hsub huE hu
  rw [← Set.insert_sdiff_singleton_comm hvx] at h
  exact h

/-- Equations (3.6) and (3.9), on the `B` side. `R = B - b₂ + a₁` and `Q = B - b₁ + a₁` are
bases, `a₂` is spanned by `Q - b₂`, and `Q - y + a₂` is a basis. Then `R - y + a₂` is a basis. -/
theorem kz_right {B : Set α} {a₁ a₂ b₁ b₂ y : α} (hR : M.IsBase (insert a₁ (B \ {b₂})))
    (hQ : M.IsBase (insert a₁ (B \ {b₁}))) (ha₂E : a₂ ∈ M.E) (ha₂B : a₂ ∉ B) (h12 : a₂ ≠ a₁)
    (ha₁b₁ : a₁ ≠ b₁) (h33 : ¬ M.IsBase (insert a₂ (insert a₁ (B \ {b₁}) \ {b₂})))
    (hy : M.IsBase (insert a₂ (insert a₁ (B \ {b₁}) \ {y}))) :
    M.IsBase (insert a₂ (insert a₁ (B \ {b₂}) \ {y})) := by
  have ha₂Q : a₂ ∉ insert a₁ (B \ {b₁}) := by
    intro h
    rcases Set.mem_insert_iff.1 h with h | h
    · exact h12 h
    · exact ha₂B h.1
  have ha₂R : a₂ ∉ insert a₁ (B \ {b₂}) := by
    intro h
    rcases Set.mem_insert_iff.1 h with h | h
    · exact h12 h
    · exact ha₂B h.1
  have h₁ : a₂ ∈ M.closure (insert a₁ (B \ {b₂}) \ {b₁}) := by
    refine M.closure_subset_closure ?_ (mem_closure_of_not_isBase hQ ha₂E ha₂Q h33)
    rintro x ⟨hx, hxb₂⟩
    rcases Set.mem_insert_iff.1 hx with hxa | ⟨hxB, hxb₁⟩
    · rw [hxa]
      exact ⟨Set.mem_insert _ _, ha₁b₁⟩
    · exact ⟨Set.mem_insert_of_mem _ ⟨hxB, hxb₂⟩, hxb₁⟩
  have h₂ : a₂ ∉ M.closure (insert a₁ (B \ {b₂}) \ {b₁} \ {y}) := by
    intro h
    refine notMem_closure_of_isBase hQ ha₂E ha₂Q hy (M.closure_subset_closure ?_ h)
    rintro x ⟨⟨hx, hxb₁⟩, hxy⟩
    refine ⟨?_, hxy⟩
    rcases Set.mem_insert_iff.1 hx with hxa | ⟨hxB, -⟩
    · rw [hxa]
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨hxB, hxb₁⟩
  exact isBase_insert_of_closure hR ha₂E ha₂R h₁ h₂

/-- The two cases of Theorem 3.3, from the witnesses `b₂`, `b₃` of (3.1)–(3.3). -/
theorem serialPair_of_witnesses {A B : Set α} {a₁ a₂ b₁ b₂ b₃ : α} (hA : M.IsBase A)
    (hB : M.IsBase B) (hAB : Disjoint A B) (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (h12 : a₁ ≠ a₂)
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B \ {b₁}) (hb₃ : b₃ ∈ B \ {b₁})
    (hA' : M.IsBase (insert b₁ (A \ {a₁}))) (hB' : M.IsBase (insert a₁ (B \ {b₁})))
    (h4b : M.IsBase (insert a₂ (insert a₁ (B \ {b₁}) \ {a₁})))
    (h31a : M.IsBase (insert b₁ (insert a₁ (B \ {b₁}) \ {b₂})))
    (h31b : M.IsBase (insert b₂ (insert b₁ (A \ {a₁}) \ {a₂})))
    (h32a : M.IsBase (insert a₂ (insert a₁ (B \ {b₁}) \ {b₃})))
    (h32b : M.IsBase (insert b₃ (insert b₁ (A \ {a₁}) \ {b₁})))
    (h33a : ¬ M.IsBase (insert a₂ (insert a₁ (B \ {b₁}) \ {b₂})))
    (h33b : ¬ M.IsBase (insert b₃ (insert b₁ (A \ {a₁}) \ {a₂}))) :
    SerialPair M A B a₁ a₂ b₂ b₃ ∨ SerialPair M A B a₂ a₁ b₂ b₃ := by
  have ha₁B : a₁ ∉ B := Set.disjoint_left.1 hAB ha₁
  have ha₂B : a₂ ∉ B := Set.disjoint_left.1 hAB ha₂
  have hb₁A : b₁ ∉ A := Set.disjoint_right.1 hAB hb₁
  have hnP : ∀ b ∈ B \ {b₁}, b ∉ insert b₁ (A \ {a₁}) := by
    rintro b ⟨hbB, hbb₁⟩ h
    rcases Set.mem_insert_iff.1 h with h | h
    · exact hbb₁ h
    · exact Set.disjoint_left.1 hAB h.1 hbB
  have hb₂E : b₂ ∈ M.E := hB.subset_ground hb₂.1
  have ha₂b₁ : a₂ ≠ b₁ := fun h => hb₁A (by rw [← h]; exact ha₂)
  have ha₁b₁ : a₁ ≠ b₁ := fun h => hb₁A (by rw [← h]; exact ha₁)
  have ha₁b₂ : a₁ ≠ b₂ := fun h => ha₁B (by rw [h]; exact hb₂.1)
  have ha₁b₃ : a₁ ≠ b₃ := fun h => ha₁B (by rw [h]; exact hb₃.1)
  have hb₁₂ : b₁ ∈ B \ {b₂} := ⟨hb₁, fun h => hb₂.2 (Set.mem_singleton_iff.1 h).symm⟩
  have hb₁A' : b₁ ∉ A \ {a₁} := fun h => hb₁A h.1
  have ha₁B₂ : a₁ ∉ B \ {b₂} := fun h => ha₁B h.1
  have ha₂P : a₂ ∈ insert b₁ (A \ {a₁}) := Set.mem_insert_of_mem _ ⟨ha₂, h12.symm⟩
  -- `B' - b₂ + b₁ = B - b₂ + a₁`
  have hQeq : insert b₁ (insert a₁ (B \ {b₁}) \ {b₂}) = insert a₁ (B \ {b₂}) := by
    rw [← Set.insert_sdiff_singleton_comm ha₁b₂, Set.insert_comm, Set.sdiff_sdiff_comm,
      Set.insert_sdiff_self_of_mem hb₁₂]
  have hR : M.IsBase (insert a₁ (B \ {b₂})) := by
    rw [← hQeq]
    exact h31a
  -- (3.5)
  have hfinA := kz_final_left hA' ha₂P ha₂b₁ hb₂E (hnP b₂ hb₂) (hB.subset_ground hb₃.1)
    (hnP b₃ hb₃) h31b h32b h33b
  rw [Set.insert_sdiff_self_of_notMem hb₁A'] at hfinA
  -- (3.6)
  have hfinB := kz_right hR hB' (hA.subset_ground ha₂) ha₂B h12.symm ha₁b₁ h33a h32a
  rw [← Set.insert_sdiff_singleton_comm ha₁b₃] at hfinB
  by_cases hcase : M.IsBase (insert b₂ (A \ {a₁}))
  · -- Case 1: the first exchange is `(a₁, b₂)`
    refine Or.inl ⟨hcase, hR, hfinA, ?_⟩
    rw [Set.insert_comm]
    exact hfinB
  · -- Case 2: the first exchange is `(a₂, b₂)`
    have hb₂A : b₂ ∉ A := Set.disjoint_right.1 hAB hb₂.1
    have hc2A : M.IsBase (insert b₂ (A \ {a₂})) := by
      refine isBase_insert_of_closure hA hb₂E hb₂A
        (mem_closure_of_not_isBase hA hb₂E hb₂A hcase) ?_
      intro h
      exact notMem_closure_of_isBase hA' hb₂E (hnP b₂ hb₂) h31b
        (M.closure_subset_closure (Set.sdiff_subset_sdiff_left (Set.subset_insert b₁ _)) h)
    have hc2B := kz_right hR hB' (hA.subset_ground ha₂) ha₂B h12.symm ha₁b₁ h33a h4b
    rw [Set.insert_sdiff_self_of_notMem ha₁B₂] at hc2B
    refine Or.inr ⟨hc2A, hc2B, ?_, hfinB⟩
    rw [Set.sdiff_sdiff_comm]
    exact hfinA

/-- **Theorem 3.3.** For disjoint bases `A`, `B` and distinct `a₁, a₂ ∈ A`, the pair
`{a₁, a₂}` has a serial symmetric exchange with a pair `{y₁, y₂} ⊆ B`, in one of the two
orders of `a₁, a₂`. -/
theorem exists_serialPair {A B : Set α} {a₁ a₂ : α} (hA : M.IsBase A) (hB : M.IsBase B)
    (hAB : Disjoint A B) (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (h12 : a₁ ≠ a₂) :
    ∃ y₁ ∈ B, ∃ y₂ ∈ B, y₁ ≠ y₂ ∧
      (SerialPair M A B a₁ a₂ y₁ y₂ ∨ SerialPair M A B a₂ a₁ y₁ y₂) := by
  obtain ⟨b₁, hb₁, hA', hB'⟩ := exists_symm_exchange hA hB hAB ha₁
  have ha₁B : a₁ ∉ B := Set.disjoint_left.1 hAB ha₁
  have hb₁A : b₁ ∉ A := Set.disjoint_right.1 hAB hb₁
  have hPQ := disjoint_exchange hAB ha₁ hb₁
  have ha₂P : a₂ ∈ insert b₁ (A \ {a₁}) := Set.mem_insert_of_mem _ ⟨ha₂, h12.symm⟩
  by_cases hex : ∃ b ∈ B, b ≠ b₁ ∧ M.IsBase (insert b (insert b₁ (A \ {a₁}) \ {a₂})) ∧
      M.IsBase (insert a₂ (insert a₁ (B \ {b₁}) \ {b}))
  · obtain ⟨b, hb, hbb₁, h₃, h₄⟩ := hex
    exact ⟨b₁, hb₁, b, hb, fun h => hbb₁ h.symm,
      Or.inl (serialPair_of_second hAB ha₁ ha₂ hb₁ hb hA' hB' h₃ h₄)⟩
  -- otherwise `a₂` can only be exchanged with `a₁`
  have hno : ∀ b ∈ insert a₁ (B \ {b₁}), b ≠ a₁ →
      M.IsBase (insert b (insert b₁ (A \ {a₁}) \ {a₂})) →
      ¬ M.IsBase (insert a₂ (insert a₁ (B \ {b₁}) \ {b})) := by
    intro b hb hba h₃ h₄
    rcases Set.mem_insert_iff.1 hb with h | ⟨hbB, hbb₁⟩
    · exact hba h
    · exact hex ⟨b, hbB, hbb₁, h₃, h₄⟩
  obtain ⟨z, hz, hz₁, hz₂⟩ := exists_symm_exchange hA' hB' hPQ ha₂P
  have hza : z = a₁ := by
    by_contra hza
    exact hno z hz hza hz₁ hz₂
  rw [hza] at hz₁ hz₂
  have ha₁B' : a₁ ∉ B \ {b₁} := fun h => ha₁B h.1
  have hb₁A' : b₁ ∉ A \ {a₁} := fun h => hb₁A h.1
  have hBeq : insert b₁ (insert a₁ (B \ {b₁}) \ {a₁}) = B := by
    rw [Set.insert_sdiff_self_of_notMem ha₁B', Set.insert_sdiff_self_of_mem hb₁]
  have hAeq : insert a₁ (insert b₁ (A \ {a₁}) \ {b₁}) = A := by
    rw [Set.insert_sdiff_self_of_notMem hb₁A', Set.insert_sdiff_self_of_mem ha₁]
  have hBB : M.IsBase (insert b₁ (insert a₁ (B \ {b₁}) \ {a₁})) := by
    rw [hBeq]
    exact hB
  have hAA : M.IsBase (insert a₁ (insert b₁ (A \ {a₁}) \ {b₁})) := by
    rw [hAeq]
    exact hA
  obtain ⟨b₂, hb₂, b₃, hb₃, hb₂a, hb₃a, h23, h31a, h31b, h32a, h32b, h33a, h33b⟩ :=
    kz_witnesses hA' hB' hPQ ha₂P (Set.mem_insert _ _) (fun h => hb₁A (by rw [← h]; exact ha₂))
      (Set.mem_insert _ _) hBB hAA hz₁ hz₂ hno
  have hb₂' : b₂ ∈ B \ {b₁} := (Set.mem_insert_iff.1 hb₂).resolve_left hb₂a
  have hb₃' : b₃ ∈ B \ {b₁} := (Set.mem_insert_iff.1 hb₃).resolve_left hb₃a
  exact ⟨b₂, hb₂'.1, b₃, hb₃'.1, h23, serialPair_of_witnesses hA hB hAB ha₁ ha₂ h12 hb₁ hb₂'
    hb₃' hA' hB' hz₂ h31a h31b h32a h32b h33a h33b⟩

/-! ### Section 4: rank four -/

/-- Equality of two set literals that list the same elements in different orders. -/
macro "set_perm" : tactic =>
  `(tactic| (ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; try tauto))

theorem isBase_of_eq {X Y : Set α} (h : M.IsBase X) (e : X = Y) : M.IsBase Y := e ▸ h

/-- In rank four a basis has four elements. -/
theorem ncard_eq_four {B : Set α} (hB : M.IsBase B) (hr : M.eRank = 4) : B.ncard = 4 := by
  have h4 : B.encard = 4 := by rw [hB.encard_eq_eRank, hr]
  have hfin : B.Finite := Set.finite_of_encard_eq_coe (k := 4) (h4.trans (by norm_num))
  rw [← hfin.cast_ncard_eq] at h4
  exact_mod_cast h4

/-- A four-element set has a third element besides two given ones. -/
theorem exists_third {A : Set α} (hA : A.ncard = 4) {x y : α} (hxy : x ≠ y) :
    ∃ z ∈ A, z ≠ x ∧ z ≠ y := by
  have h2 : ({x, y} : Set α).ncard = 2 := Set.ncard_pair hxy
  obtain ⟨z, hzA, hz⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := {x, y}) (t := A)
    (by rw [h2, hA]; norm_num)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
  exact ⟨z, hzA, hz.1, hz.2⟩

/-- A four-element set containing three distinct elements `x, y, z` is `{x, y, z, w}`. -/
theorem exists_fourth {A : Set α} (hA : A.ncard = 4) {x y z : α} (hx : x ∈ A) (hy : y ∈ A)
    (hz : z ∈ A) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ w ∈ A, w ≠ x ∧ w ≠ y ∧ w ≠ z ∧ A = {x, y, z, w} := by
  have hsub : ({x, y, z} : Set α) ⊆ A := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl <;> assumption
  have hxyz : x ∉ ({y, z} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxy, hxz⟩
  have h3 : ({x, y, z} : Set α).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem hxyz, Set.ncard_pair hyz]
  have h1 : (A \ {x, y, z}).ncard = 1 := by
    rw [Set.ncard_sdiff hsub, hA, h3]
  obtain ⟨w, hw⟩ := Set.ncard_eq_one.1 h1
  have hwA : w ∈ A \ {x, y, z} := by
    rw [hw]
    exact Set.mem_singleton w
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hwA
  obtain ⟨hwA, hwx, hwy, hwz⟩ := hwA
  refine ⟨w, hwA, hwx, hwy, hwz, ?_⟩
  ext u
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hu
    by_contra hne
    simp only [not_or] at hne
    have hu' : u ∈ A \ {x, y, z} := by
      refine ⟨hu, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne.1, hne.2.1, hne.2.2.1⟩
    rw [hw] at hu'
    exact hne.2.2.2 hu'
  · rintro (rfl | rfl | rfl | rfl) <;> assumption

/-- A full serial symmetric exchange between the bases `A` and `B` of a rank-4 matroid. -/
abbrev FullSerial (M : Matroid α) (A B : Set α) : Prop :=
  ∃ p₁ p₂ p₃ p₄ q₁ q₂ q₃ q₄ : α, A = {p₁, p₂, p₃, p₄} ∧ B = {q₁, q₂, q₃, q₄} ∧
    (p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₁ ≠ p₄ ∧ p₂ ≠ p₃ ∧ p₂ ≠ p₄ ∧ p₃ ≠ p₄) ∧
    (q₁ ≠ q₂ ∧ q₁ ≠ q₃ ∧ q₁ ≠ q₄ ∧ q₂ ≠ q₃ ∧ q₂ ≠ q₄ ∧ q₃ ≠ q₄) ∧
    M.IsBase {q₁, p₂, p₃, p₄} ∧ M.IsBase {q₁, q₂, p₃, p₄} ∧ M.IsBase {q₁, q₂, q₃, p₄} ∧
    M.IsBase {p₁, q₂, q₃, q₄} ∧ M.IsBase {p₁, p₂, q₃, q₄} ∧ M.IsBase {p₁, p₂, p₃, q₄}

/-- **Proposition 4.1.** A serial symmetric exchange `(x₁, y₁), (x₂, y₂)` and a symmetric
exchange `(a, b)` among the remaining elements give a full serial symmetric exchange:
`x₁ x₂ w a` against `y₁ y₂ v b`, where `w` and `v` are the fourth elements. -/
theorem fullSerial_of_serialPair {A B : Set α} {x₁ x₂ y₁ y₂ a b : α} (hA4 : A.ncard = 4)
    (hB4 : B.ncard = 4) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hx : x₁ ≠ x₂) (hy₁ : y₁ ∈ B)
    (hy₂ : y₂ ∈ B) (hy : y₁ ≠ y₂) (ha : a ∈ A) (ha₁ : a ≠ x₁) (ha₂ : a ≠ x₂) (hb : b ∈ B)
    (hb₁ : b ≠ y₁) (hb₂ : b ≠ y₂) (hS : SerialPair M A B x₁ x₂ y₁ y₂)
    (hab : M.IsBase (insert b (A \ {a}))) (hba : M.IsBase (insert a (B \ {b}))) :
    FullSerial M A B := by
  obtain ⟨w, -, hwx₁, hwx₂, hwa, hAeq⟩ := exists_fourth hA4 hx₁ hx₂ ha hx ha₁.symm ha₂.symm
  obtain ⟨v, -, hvy₁, hvy₂, hvb, hBeq⟩ := exists_fourth hB4 hy₁ hy₂ hb hy hb₁.symm hb₂.symm
  have hA' : A = {a, x₁, x₂, w} := by rw [hAeq]; set_perm
  have hB' : B = {b, y₁, y₂, v} := by rw [hBeq]; set_perm
  have r₁ : ({x₁, x₂, a, w} : Set α) \ {x₁} = {x₂, a, w} := by
    apply Set.insert_sdiff_self_of_notMem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hx, ha₁.symm, hwx₁.symm⟩
  have r₂ : ({x₂, a, w} : Set α) \ {x₂} = {a, w} := by
    apply Set.insert_sdiff_self_of_notMem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ha₂.symm, hwx₂.symm⟩
  have r₃ : ({a, x₁, x₂, w} : Set α) \ {a} = {x₁, x₂, w} := by
    apply Set.insert_sdiff_self_of_notMem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ha₁, ha₂, hwa.symm⟩
  have s₁ : ({y₁, y₂, b, v} : Set α) \ {y₁} = {y₂, b, v} := by
    apply Set.insert_sdiff_self_of_notMem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hy, hb₁.symm, hvy₁.symm⟩
  have s₂ : ({y₂, b, v} : Set α) \ {y₂} = {b, v} := by
    apply Set.insert_sdiff_self_of_notMem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hb₂.symm, hvy₂.symm⟩
  have s₃ : ({b, y₁, y₂, v} : Set α) \ {b} = {y₁, y₂, v} := by
    apply Set.insert_sdiff_self_of_notMem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hb₁, hb₂, hvb.symm⟩
  have h1 := hS.base₁
  have h2 := hS.base₁'
  have h3 := hS.base₂
  have h4 := hS.base₂'
  rw [hAeq, r₁] at h1
  rw [hBeq, s₁] at h2
  rw [hAeq, r₁, r₂] at h3
  rw [hBeq, s₁, s₂] at h4
  rw [hA', r₃] at hab
  rw [hB', s₃] at hba
  refine ⟨x₁, x₂, w, a, y₁, y₂, v, b, (by rw [hAeq]; set_perm), (by rw [hBeq]; set_perm),
    ⟨hx, hwx₁.symm, ha₁.symm, hwx₂.symm, ha₂.symm, hwa⟩,
    ⟨hy, hvy₁.symm, hb₁.symm, hvy₂.symm, hb₂.symm, hvb⟩,
    isBase_of_eq h1 (by set_perm), isBase_of_eq h3 (by set_perm), isBase_of_eq hba (by set_perm),
    isBase_of_eq h2 (by set_perm), isBase_of_eq h4 (by set_perm), isBase_of_eq hab (by set_perm)⟩

/-- The second half of Theorem 4.2: no symmetric exchange between `{a₃, a₄}` and `{y₃, y₄}`. -/
theorem fullSerial_of_no_exchange {A B : Set α} {a₃ a₄ y₃ y₄ : α} (hA : M.IsBase A)
    (hB : M.IsBase B) (hAB : Disjoint A B) (hA4 : A.ncard = 4) (hB4 : B.ncard = 4)
    (ha₃ : a₃ ∈ A) (ha₄ : a₄ ∈ A) (ha : a₃ ≠ a₄) (hy₃ : y₃ ∈ B) (hy₄ : y₄ ∈ B) (hy : y₃ ≠ y₄)
    (hno : ∀ a b, (a = a₃ ∨ a = a₄) → (b = y₃ ∨ b = y₄) → M.IsBase (insert b (A \ {a})) →
      ¬ M.IsBase (insert a (B \ {b}))) :
    FullSerial M A B := by
  -- Theorem 3.3 for `{a₃, a₄}`
  obtain ⟨w₁, hw₁, w₂, hw₂, hw, hS'⟩ := exists_serialPair hA hB hAB ha₃ ha₄ ha
  obtain ⟨z₁, z₂, hz, hzS⟩ : ∃ z₁ z₂, ((z₁ = a₃ ∧ z₂ = a₄) ∨ (z₁ = a₄ ∧ z₂ = a₃)) ∧
      SerialPair M A B z₁ z₂ w₁ w₂ := by
    rcases hS' with h | h
    · exact ⟨a₃, a₄, Or.inl ⟨rfl, rfl⟩, h⟩
    · exact ⟨a₄, a₃, Or.inr ⟨rfl, rfl⟩, h⟩
  have hz₁ : z₁ = a₃ ∨ z₁ = a₄ := hz.imp And.left And.left
  -- the first exchange `(z₁, w₁)` does not use `y₃` or `y₄`
  have hw₁₃ : w₁ ≠ y₃ := fun h => hno z₁ w₁ hz₁ (Or.inl h) hzS.base₁ hzS.base₁'
  have hw₁₄ : w₁ ≠ y₄ := fun h => hno z₁ w₁ hz₁ (Or.inr h) hzS.base₁ hzS.base₁'
  -- so some `b ∈ {y₃, y₄}` avoids both `w₁` and `w₂`
  obtain ⟨b, hb, hbw₂⟩ : ∃ b, (b = y₃ ∨ b = y₄) ∧ b ≠ w₂ := by
    by_cases h : y₃ = w₂
    · exact ⟨y₄, Or.inr rfl, fun h' => hy (h.trans h'.symm)⟩
    · exact ⟨y₃, Or.inl rfl, h⟩
  have hbB : b ∈ B := by
    rcases hb with h | h
    · rw [h]; exact hy₃
    · rw [h]; exact hy₄
  have hbw₁ : b ≠ w₁ := by
    rcases hb with h | h
    · rw [h]; exact fun h' => hw₁₃ h'.symm
    · rw [h]; exact fun h' => hw₁₄ h'.symm
  -- a symmetric exchange partner of `b` (Observation 2.3); it is not `a₃` or `a₄`
  obtain ⟨a, haA, hba, hab⟩ := exists_symm_exchange hB hA hAB.symm hbB
  have ha' : ¬ (a = a₃ ∨ a = a₄) := fun h => hno a b h hb hab hba
  have hzA : z₁ ∈ A ∧ z₂ ∈ A ∧ z₁ ≠ z₂ ∧ a ≠ z₁ ∧ a ≠ z₂ := by
    rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha₃, ha₄, ha, fun h => ha' (Or.inl h), fun h => ha' (Or.inr h)⟩
    · exact ⟨ha₄, ha₃, fun h => ha h.symm, fun h => ha' (Or.inr h), fun h => ha' (Or.inl h)⟩
  obtain ⟨hz₁A, hz₂A, hz12, haz₁, haz₂⟩ := hzA
  exact fullSerial_of_serialPair hA4 hB4 hz₁A hz₂A hz12 hw₁ hw₂ hw haA haz₁ haz₂ hbB hbw₁ hbw₂
    hzS hab hba

/-- **Kotlar–Ziv, Theorem 4.2.** Two disjoint bases `A`, `B` of a rank-4 matroid have a full
serial symmetric exchange. There are enumerations `A = {p₁, p₂, p₃, p₄}` and
`B = {q₁, q₂, q₃, q₄}` such that for `i = 1, 2, 3` both `(A - {p₁ … pᵢ}) + {q₁ … qᵢ}` and
`(B - {q₁ … qᵢ}) + {p₁ … pᵢ}` are bases. For `i = 0` and `i = 4` these sets are `A` and `B`. -/
theorem serial_exchange_rank_four {A B : Set α} (hA : M.IsBase A) (hB : M.IsBase B)
    (hAB : Disjoint A B) (hr : M.eRank = 4) :
    ∃ p₁ p₂ p₃ p₄ q₁ q₂ q₃ q₄ : α, A = {p₁, p₂, p₃, p₄} ∧ B = {q₁, q₂, q₃, q₄} ∧
      (p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₁ ≠ p₄ ∧ p₂ ≠ p₃ ∧ p₂ ≠ p₄ ∧ p₃ ≠ p₄) ∧
      (q₁ ≠ q₂ ∧ q₁ ≠ q₃ ∧ q₁ ≠ q₄ ∧ q₂ ≠ q₃ ∧ q₂ ≠ q₄ ∧ q₃ ≠ q₄) ∧
      M.IsBase {q₁, p₂, p₃, p₄} ∧ M.IsBase {q₁, q₂, p₃, p₄} ∧ M.IsBase {q₁, q₂, q₃, p₄} ∧
      M.IsBase {p₁, q₂, q₃, q₄} ∧ M.IsBase {p₁, p₂, q₃, q₄} ∧ M.IsBase {p₁, p₂, p₃, q₄} := by
  have hA4 := ncard_eq_four hA hr
  have hB4 := ncard_eq_four hB hr
  obtain ⟨a₁, ha₁⟩ : A.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hA4]; norm_num)
  obtain ⟨a₂, ha₂, h21⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hA4]; norm_num) a₁
  -- a serial symmetric exchange of `{a₁, a₂}` (Theorem 3.3)
  obtain ⟨x₁, x₂, y₁, y₂, hx₁, hx₂, hx, hy₁, hy₂, hy, hS⟩ : ∃ x₁ x₂ y₁ y₂, x₁ ∈ A ∧ x₂ ∈ A ∧
      x₁ ≠ x₂ ∧ y₁ ∈ B ∧ y₂ ∈ B ∧ y₁ ≠ y₂ ∧ SerialPair M A B x₁ x₂ y₁ y₂ := by
    obtain ⟨y₁, hy₁, y₂, hy₂, hy, hS | hS⟩ := exists_serialPair hA hB hAB ha₁ ha₂ h21.symm
    · exact ⟨a₁, a₂, y₁, y₂, ha₁, ha₂, h21.symm, hy₁, hy₂, hy, hS⟩
    · exact ⟨a₂, a₁, y₁, y₂, ha₂, ha₁, h21, hy₁, hy₂, hy, hS⟩
  -- the remaining elements `a₃, a₄` of `A` and `y₃, y₄` of `B`
  obtain ⟨a₃, ha₃, ha₃x₁, ha₃x₂⟩ := exists_third hA4 hx
  obtain ⟨a₄, ha₄, ha₄x₁, ha₄x₂, ha₄a₃, -⟩ :=
    exists_fourth hA4 hx₁ hx₂ ha₃ hx ha₃x₁.symm ha₃x₂.symm
  obtain ⟨y₃, hy₃, hy₃y₁, hy₃y₂⟩ := exists_third hB4 hy
  obtain ⟨y₄, hy₄, hy₄y₁, hy₄y₂, hy₄y₃, -⟩ :=
    exists_fourth hB4 hy₁ hy₂ hy₃ hy hy₃y₁.symm hy₃y₂.symm
  by_cases hex : ∃ a b, (a = a₃ ∨ a = a₄) ∧ (b = y₃ ∨ b = y₄) ∧
      M.IsBase (insert b (A \ {a})) ∧ M.IsBase (insert a (B \ {b}))
  · -- Proposition 4.1 directly
    obtain ⟨a, b, ha, hb, hab, hba⟩ := hex
    have haA : a ∈ A ∧ a ≠ x₁ ∧ a ≠ x₂ := by
      rcases ha with h | h
      · rw [h]; exact ⟨ha₃, ha₃x₁, ha₃x₂⟩
      · rw [h]; exact ⟨ha₄, ha₄x₁, ha₄x₂⟩
    have hbB : b ∈ B ∧ b ≠ y₁ ∧ b ≠ y₂ := by
      rcases hb with h | h
      · rw [h]; exact ⟨hy₃, hy₃y₁, hy₃y₂⟩
      · rw [h]; exact ⟨hy₄, hy₄y₁, hy₄y₂⟩
    exact fullSerial_of_serialPair hA4 hB4 hx₁ hx₂ hx hy₁ hy₂ hy haA.1 haA.2.1 haA.2.2 hbB.1
      hbB.2.1 hbB.2.2 hS hab hba
  · exact fullSerial_of_no_exchange hA hB hAB hA4 hB4 ha₃ ha₄ (fun h => ha₄a₃ h.symm) hy₃ hy₄
      (fun h => hy₄y₃ h.symm) fun a b ha hb h₁ h₂ => hex ⟨a, b, ha, hb, h₁, h₂⟩

/-- Theorem 4.2 as a cyclic basis ordering: the eight cyclic 4-windows of
`p₁ p₂ p₃ p₄ q₁ q₂ q₃ q₄` are bases. -/
theorem cyclic_windows_rank_four {A B : Set α} (hA : M.IsBase A) (hB : M.IsBase B)
    (hAB : Disjoint A B) (hr : M.eRank = 4) :
    ∃ p₁ p₂ p₃ p₄ q₁ q₂ q₃ q₄ : α, A = {p₁, p₂, p₃, p₄} ∧ B = {q₁, q₂, q₃, q₄} ∧
      M.IsBase {p₁, p₂, p₃, p₄} ∧ M.IsBase {p₂, p₃, p₄, q₁} ∧ M.IsBase {p₃, p₄, q₁, q₂} ∧
      M.IsBase {p₄, q₁, q₂, q₃} ∧ M.IsBase {q₁, q₂, q₃, q₄} ∧ M.IsBase {q₂, q₃, q₄, p₁} ∧
      M.IsBase {q₃, q₄, p₁, p₂} ∧ M.IsBase {q₄, p₁, p₂, p₃} := by
  obtain ⟨p₁, p₂, p₃, p₄, q₁, q₂, q₃, q₄, hAe, hBe, -, -, h1, h2, h3, h4, h5, h6⟩ :=
    serial_exchange_rank_four hA hB hAB hr
  exact ⟨p₁, p₂, p₃, p₄, q₁, q₂, q₃, q₄, hAe, hBe, isBase_of_eq hA hAe,
    isBase_of_eq h1 (by set_perm), isBase_of_eq h2 (by set_perm), isBase_of_eq h3 (by set_perm),
    isBase_of_eq hB hBe, isBase_of_eq h4 (by set_perm), isBase_of_eq h5 (by set_perm),
    isBase_of_eq h6 (by set_perm)⟩

#print axioms serial_exchange_rank_four
#print axioms cyclic_windows_rank_four

end HigherRankKUM.KotlarZiv
