import Rank3KUM.HalfWeave.Indexing

namespace Rank3KUM.HalfWeave

/-- The finite fiber of a block label. -/
def fiberFinset {n m : ℕ}
    (block : Fin n → Fin m) (c : Fin m) :
    Finset (Fin n) :=
  Finset.univ.filter fun j => block j = c

/-- A flattened sequence of contiguous blocks, ordered by nonincreasing size. -/
structure SortedBlockModel (k m : ℕ) where
  block : Fin (2 * k) → Fin m
  monotone_block : Monotone block
  surjective_block : Function.Surjective block
  two_le_m : 2 ≤ m
  fiber_card_le :
    ∀ c, (fiberFinset block c).card ≤ k
  fiber_card_antitone :
    Antitone fun c => (fiberFinset block c).card

/-- A monotone fiber contains the full interval between any two of its members. -/
theorem monotone_fiber_interval
    {n m : ℕ}
    (block : Fin n → Fin m)
    (hmono : Monotone block)
    {a b j : Fin n}
    (_hab : a ≤ b)
    (heq : block a = block b)
    (haj : a ≤ j)
    (hjb : j ≤ b) :
    block j = block a := by
  apply le_antisymm
  · simpa [heq] using hmono hjb
  · exact hmono haj

/--
If a monotone fiber contains `a ≤ b`, then it has at least
`b.val - a.val + 1` members.
-/
theorem fiber_card_ge_interval
    {n m : ℕ}
    (block : Fin n → Fin m)
    (hmono : Monotone block)
    {a b : Fin n}
    (hab : a ≤ b)
    (heq : block a = block b) :
    b.val - a.val + 1 ≤
      (fiberFinset block (block a)).card := by
  have hsub :
      Finset.Icc a b ⊆
        fiberFinset block (block a) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    simp only [fiberFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact monotone_fiber_interval block hmono
      hab heq hj.1 hj.2
  have hc := Finset.card_le_card hsub
  have hIcc :
      (Finset.Icc a b).card =
        b.val - a.val + 1 := by
    simp
    omega
  rw [hIcc] at hc
  exact hc

/-- Paired first- and second-half indices have different block labels. -/
theorem first_second_blocks_ne
    {k m : ℕ}
    (S : SortedBlockModel k m)
    (i : Fin k) :
    S.block (firstIndex k i) ≠
      S.block (secondIndex k i) := by
  intro heq
  have hab :
      firstIndex k i ≤ secondIndex k i := by
    change i.val ≤ k + i.val
    omega
  have hlower :=
    fiber_card_ge_interval S.block
      S.monotone_block hab heq
  have hupper :=
    S.fiber_card_le
      (S.block (firstIndex k i))
  have hlower' :
      k + 1 ≤
        (fiberFinset S.block
          (S.block (firstIndex k i))).card := by
    simpa [firstIndex, secondIndex] using hlower
  omega

/-- Away from the final index, cyclic successor has raw value `i+1`. -/
theorem cyclicSucc_val_of_ne_last
    (k : ℕ) (hk : 0 < k) (i : Fin k)
    (hi : i ≠ lastFin k hk) :
    (cyclicSucc k hk i).val = i.val + 1 := by
  have hneval : i.val ≠ k - 1 := by
    intro hval
    apply hi
    apply Fin.ext
    simpa [lastFin] using hval
  have hlt : i.val + 1 < k := by
    omega
  rw [cyclicSucc_val, Nat.mod_eq_of_lt hlt]

/--
For a nonfinal `i`, the second-half index `k+i` and next first-half index
`i+1` have different block labels.
-/
theorem second_next_blocks_ne_nonfinal
    {k m : ℕ}
    (hk : 0 < k)
    (S : SortedBlockModel k m)
    (i : Fin k)
    (hi : i ≠ lastFin k hk) :
    S.block (secondIndex k i) ≠
      S.block (firstIndex k (cyclicSucc k hk i)) := by
  intro heq_ba
  let p : Fin (2 * k) := firstIndex k i
  let a : Fin (2 * k) :=
    firstIndex k (cyclicSucc k hk i)
  let b : Fin (2 * k) := secondIndex k i

  have hsuccval :
      (cyclicSucc k hk i).val = i.val + 1 :=
    cyclicSucc_val_of_ne_last k hk i hi
  have hi_succ_lt : i.val + 1 < k := by
    have hneval : i.val ≠ k - 1 := by
      intro hval
      apply hi
      apply Fin.ext
      simpa [lastFin] using hval
    omega

  have hab : a ≤ b := by
    change (cyclicSucc k hk i).val ≤ k + i.val
    rw [hsuccval]
    omega
  have heq_ab : S.block a = S.block b :=
    heq_ba.symm
  have hmid_lower_raw :=
    fiber_card_ge_interval S.block S.monotone_block
      hab heq_ab
  change
    (k + i.val) - (cyclicSucc k hk i).val + 1 ≤
      (fiberFinset S.block (S.block a)).card
    at hmid_lower_raw
  rw [hsuccval] at hmid_lower_raw
  have hmid_lower :
      k ≤ (fiberFinset S.block (S.block a)).card := by
    omega

  have hmid_upper :=
    S.fiber_card_le (S.block a)
  have hmid_eq :
      (fiberFinset S.block (S.block a)).card = k := by
    omega

  have hp_ne_a : S.block p ≠ S.block a := by
    intro heq_pa
    have hpb : S.block p = S.block b :=
      heq_pa.trans heq_ab
    have hpb_order : p ≤ b := by
      change i.val ≤ k + i.val
      omega
    have hlong :=
      fiber_card_ge_interval S.block S.monotone_block
        hpb_order hpb
    change
      (k + i.val) - i.val + 1 ≤
        (fiberFinset S.block (S.block p)).card
      at hlong
    have hlong' :
        k + 1 ≤
          (fiberFinset S.block (S.block p)).card := by
      omega
    have hp_upper :=
      S.fiber_card_le (S.block p)
    omega

  have hp_le_a : p ≤ a := by
    change i.val ≤ (cyclicSucc k hk i).val
    rw [hsuccval]
    omega
  have hlabel_le :
      S.block p ≤ S.block a :=
    S.monotone_block hp_le_a
  have hlabel_lt :
      S.block p < S.block a :=
    lt_of_le_of_ne hlabel_le hp_ne_a

  have hsize_order :
      (fiberFinset S.block (S.block a)).card ≤
        (fiberFinset S.block (S.block p)).card :=
    S.fiber_card_antitone hlabel_lt.le
  have hprev_lower :
      k ≤ (fiberFinset S.block (S.block p)).card := by
    omega

  have hprev_sub :
      fiberFinset S.block (S.block p) ⊆
        Finset.Iic p := by
    intro j hj
    have hjlabel : S.block j = S.block p := by
      simpa [fiberFinset] using hj
    rw [Finset.mem_Iic]
    by_contra hnot
    have hp_lt_j : p < j :=
      lt_of_not_ge hnot
    have ha_le_j : a ≤ j := by
      change (cyclicSucc k hk i).val ≤ j.val
      change i.val < j.val at hp_lt_j
      rw [hsuccval]
      omega
    have hbad :
        S.block a ≤ S.block p := by
      have hjmono := S.monotone_block ha_le_j
      simpa [hjlabel] using hjmono
    exact (not_le_of_gt hlabel_lt) hbad

  have hprev_card_upper :=
    Finset.card_le_card hprev_sub
  have hIic :
      (Finset.Iic p).card = p.val + 1 := by
    simp
  rw [hIic] at hprev_card_upper
  have hprev_upper :
      (fiberFinset S.block (S.block p)).card ≤
        i.val + 1 := by
    simpa [p, firstIndex] using hprev_card_upper
  omega

/-- The final second-half index and first index zero have different labels. -/
theorem wraparound_blocks_ne
    {k m : ℕ}
    (hk : 0 < k)
    (S : SortedBlockModel k m) :
    S.block (secondIndex k (lastFin k hk)) ≠
      S.block (firstIndex k (zeroFin k hk)) := by
  intro heq_ba
  let a : Fin (2 * k) :=
    firstIndex k (zeroFin k hk)
  let b : Fin (2 * k) :=
    secondIndex k (lastFin k hk)
  have hab : a ≤ b := by
    change 0 ≤ k + (k - 1)
    omega
  have heq_ab : S.block a = S.block b :=
    heq_ba.symm
  have hlong :=
    fiber_card_ge_interval S.block S.monotone_block
      hab heq_ab
  change
    (k + (k - 1)) - 0 + 1 ≤
      (fiberFinset S.block (S.block a)).card
    at hlong
  have htwo :
      2 * k ≤
        (fiberFinset S.block (S.block a)).card := by
    omega
  have hupper :=
    S.fiber_card_le (S.block a)
  omega

/-- Every successor adjacency in the half weave crosses different blocks. -/
theorem woven_successor_blocks_ne
    {k m : ℕ}
    (hk : 0 < k)
    (S : SortedBlockModel k m)
    (p : Fin k × Bool) :
    S.block (halfWeaveEquiv k hk p) ≠
      S.block
        (halfWeaveEquiv k hk (weaveNext k hk p)) := by
  have hadj :=
    woven_successor_adjacency
      k hk (Equiv.refl (Fin (2 * k))) p
  rcases hadj with
      ⟨i, _hp, hpair⟩ | ⟨i, _hp, hpair⟩
  · have hindex :
        (halfWeaveEquiv k hk p,
         halfWeaveEquiv k hk (weaveNext k hk p)) =
        (firstIndex k i, secondIndex k i) := by
      simpa [woven] using hpair
    have hfirst := congrArg Prod.fst hindex
    have hsecond := congrArg Prod.snd hindex
    have hfirst' :
        halfWeaveEquiv k hk p = firstIndex k i := by
      simpa using hfirst
    have hsecond' :
        halfWeaveEquiv k hk (weaveNext k hk p) =
          secondIndex k i := by
      simpa using hsecond
    intro heq
    apply first_second_blocks_ne S i
    rw [← hfirst', ← hsecond']
    exact heq
  · have hindex :
        (halfWeaveEquiv k hk p,
         halfWeaveEquiv k hk (weaveNext k hk p)) =
        (secondIndex k i,
         firstIndex k (cyclicSucc k hk i)) := by
      simpa [woven] using hpair
    have hfirst := congrArg Prod.fst hindex
    have hsecond := congrArg Prod.snd hindex
    have hfirst' :
        halfWeaveEquiv k hk p = secondIndex k i := by
      simpa using hfirst
    have hsecond' :
        halfWeaveEquiv k hk (weaveNext k hk p) =
          firstIndex k (cyclicSucc k hk i) := by
      simpa using hsecond
    intro heq
    have hstandard :
        S.block (secondIndex k i) =
          S.block (firstIndex k (cyclicSucc k hk i)) := by
      rw [← hfirst', ← hsecond']
      exact heq
    by_cases hi : i = lastFin k hk
    · subst i
      apply wraparound_blocks_ne hk S
      simpa using hstandard
    · exact
        (second_next_blocks_ne_nonfinal hk S i hi)
          hstandard

end Rank3KUM.HalfWeave
