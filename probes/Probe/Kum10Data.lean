import Probe.EncF

/-!
# Tables and facts of the 10-element claims

The claims of `lean_witness_f.py` on 10 elements:

* `densTab10`: uniform density, `r(X) ≥ ⌈4|X|/10⌉` (the base lemmas);
* `lightTab10`: the strict t=0 profile with no 6-plane and no 4-line (`kum10l`);
* `ranksG c`: `K = {0..5}` is a flat plane (every `K + x` has rank 4) and `r({6..9}) = c`
  (the base lemma of Theorem G);
* `ranksL4`: `F = {0..3}` is a flat line (every `F + x` has rank 3) (the base lemma of
  Theorem L4).

An exact rank `(X, r)` gives the facts `r(X) ≥ r` and `r(X) < r + 1` (`factsOfRanks`).
-/

namespace Probe.Enc

/-- `r(X) ≥ ⌈4|X|/10⌉`. -/
def densTab10 : List ℕ := [0, 1, 1, 2, 2, 2, 3, 3, 4, 4, 4]

/-- Points `≤ 2`, lines `≤ 3` and planes `≤ 5` elements, on 10 elements. -/
def lightTab10 : List ℕ := [0, 1, 1, 2, 3, 3, 4, 4, 4, 4, 4]

/-- The flat plane `{0..5}`, its extensions by `6, 7, 8, 9`, and `r({6..9}) = c`. -/
def ranksG (c : ℕ) : List (ℕ × ℕ) :=
  [(63, 3), (127, 4), (191, 4), (319, 4), (575, 4), (960, c)]

/-- The flat line `{0..3}` and its extensions by `4, …, 9`. -/
def ranksL4 : List (ℕ × ℕ) :=
  [(15, 2), (31, 3), (47, 3), (79, 3), (143, 3), (271, 3), (527, 3)]

/-- The facts `r(X) ≥ r` and `r(X) < r + 1` of each exact rank `(X, r)`. -/
def factsOfRanks : List (ℕ × ℕ) → List (ℕ × ℕ × Bool)
  | [] => []
  | (X, r) :: l => (X, r, true) :: (X, r + 1, false) :: factsOfRanks l

theorem mem_factsOfRanks_true : ∀ {l : List (ℕ × ℕ)} {X v : ℕ},
    (X, v, true) ∈ factsOfRanks l → (X, v) ∈ l
  | [], _, _, h => by simp [factsOfRanks] at h
  | (Y, r) :: l, X, v, h => by
    rcases List.mem_cons.1 h with h1 | h2
    · cases h1
      exact List.mem_cons_self ..
    · rcases List.mem_cons.1 h2 with h3 | h4
      · cases h3
      · exact List.mem_cons_of_mem _ (mem_factsOfRanks_true h4)

theorem mem_factsOfRanks_false : ∀ {l : List (ℕ × ℕ)} {X v : ℕ},
    (X, v, false) ∈ factsOfRanks l → ∃ r, (X, r) ∈ l ∧ v = r + 1
  | [], _, _, h => by simp [factsOfRanks] at h
  | (Y, r) :: l, X, v, h => by
    rcases List.mem_cons.1 h with h1 | h2
    · cases h1
    · rcases List.mem_cons.1 h2 with h3 | h4
      · cases h3
        exact ⟨r, List.mem_cons_self .., rfl⟩
      · obtain ⟨s, hs, hv⟩ := mem_factsOfRanks_false h4
        exact ⟨s, List.mem_cons_of_mem _ hs, hv⟩

theorem factT_of_ranks {r : ℕ → ℕ} {l : List (ℕ × ℕ)} (hl : ∀ X s, (X, s) ∈ l → r X = s) :
    ∀ X v, (X, v, true) ∈ factsOfRanks l → v ≤ r X := fun X v h =>
  le_of_eq (hl X v (mem_factsOfRanks_true h)).symm

theorem factF_of_ranks {r : ℕ → ℕ} {l : List (ℕ × ℕ)} (hl : ∀ X s, (X, s) ∈ l → r X = s) :
    ∀ X v, (X, v, false) ∈ factsOfRanks l → r X < v := fun X v h => by
  obtain ⟨s, hs, rfl⟩ := mem_factsOfRanks_false h
  have := hl X s hs
  omega

end Probe.Enc
