import HigherRankKUM.BalancedWindowDecomposition

namespace HigherRankKUM

open Set

noncomputable section

variable {α : Type*}

/-- Successive cyclic shifts compose by adding their offsets. -/
theorem cyclicIndex_add
    (n : ℕ) (hn : 0 < n) (i : Fin n) (a b : ℕ) :
    cyclicIndex n hn (cyclicIndex n hn i a) b =
      cyclicIndex n hn i (a + b) := by
  apply Fin.ext
  simp only [cyclicIndex_val]
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- The order of two successive cyclic shifts is immaterial. -/
theorem cyclicIndex_add_commute
    (n : ℕ) (hn : 0 < n) (i : Fin n) (a b : ℕ) :
    cyclicIndex n hn (cyclicIndex n hn i a) b =
      cyclicIndex n hn (cyclicIndex n hn i b) a := by
  rw [cyclicIndex_add, cyclicIndex_add, Nat.add_comm a b]

/--
A cyclic window of length `r*q` is the union of the `q` consecutive
length-`r` chunks beginning `r` positions apart.
-/
theorem cyclicWindow_mul_eq_iUnion_chunks
    {E : Set α} {n r q : ℕ}
    (hn : 0 < n) (hr : 0 < r)
    (σ : Fin n ≃ E) (i : Fin n) :
    cyclicWindow (r * q) hn σ i =
      ⋃ j : Fin q,
        cyclicWindow r hn σ
          (cyclicIndex n hn i (r * j.val)) := by
  ext x
  simp only [cyclicWindow, Set.mem_range, Set.mem_iUnion]
  constructor
  · rintro ⟨u, rfl⟩
    let j : Fin q := ⟨u.val / r, by
      apply (Nat.div_lt_iff_lt_mul hr).2
      simpa [Nat.mul_comm] using u.isLt⟩
    let d : Fin r := ⟨u.val % r, Nat.mod_lt _ hr⟩
    refine ⟨j, d, ?_⟩
    have hud : r * j.val + d.val = u.val := by
      dsimp [j, d]
      have h := Nat.mod_add_div u.val r
      omega
    rw [cyclicIndex_add, hud]
  · rintro ⟨j, d, rfl⟩
    have hjle : r * (j.val + 1) ≤ r * q :=
      Nat.mul_le_mul_left r (Nat.succ_le_iff.mpr j.isLt)
    have hlt : r * j.val + d.val < r * q := by
      have hstep : r * j.val + d.val < r * (j.val + 1) := by
        rw [Nat.mul_succ]
        omega
      exact hstep.trans_le hjle
    let u : Fin (r * q) := ⟨r * j.val + d.val, hlt⟩
    refine ⟨u, ?_⟩
    dsimp [u]
    rw [cyclicIndex_add]

/--
Shifting a block position by `r*j` global places preserves its within-block
offset and advances the cyclic block index by `j`.
-/
theorem cyclicIndex_blockPosition_mul
    (r k : ℕ) (hr : 0 < r) (hk : 0 < k)
    (i : Fin k) (d : Fin r) (j : ℕ) :
    cyclicIndex (r * k) (Nat.mul_pos hr hk)
        (blockPosition r k i d) (r * j) =
      blockPosition r k (cyclicIndex k hk i j) d := by
  apply Fin.ext
  simp only [cyclicIndex_val, blockPosition_val]
  have hk1 : 1 ≤ k := Nat.succ_le_iff.mpr hk
  have hr_le : r ≤ r * k := by
    simpa using Nat.mul_le_mul_left r hk1
  have hd_lt : d.val < r * k := d.isLt.trans_le hr_le
  have hblock_lt : (i.val + j) % k < k := Nat.mod_lt _ hk
  have hblock_le :
      r * (((i.val + j) % k) + 1) ≤ r * k :=
    Nat.mul_le_mul_left r (Nat.succ_le_iff.mpr hblock_lt)
  have hrhs_lt :
      d.val + r * ((i.val + j) % k) < r * k := by
    have hstep :
        d.val + r * ((i.val + j) % k) <
          r * (((i.val + j) % k) + 1) := by
      rw [Nat.mul_succ]
      omega
    exact hstep.trans_le hblock_le
  calc
    (d.val + r * i.val + r * j) % (r * k) =
        (d.val + r * (i.val + j)) % (r * k) := by
          congr 1
          ring
    _ = (d.val % (r * k) +
          (r * (i.val + j)) % (r * k)) % (r * k) := by
          rw [Nat.add_mod]
    _ = (d.val + r * ((i.val + j) % k)) % (r * k) := by
          rw [Nat.mod_eq_of_lt hd_lt, Nat.mul_mod_mul_left]
    _ = d.val + r * ((i.val + j) % k) :=
          Nat.mod_eq_of_lt hrhs_lt

/--
If a `q*(a+b)`-window starts in the left part of a period of
`(L^a R^b)^p`, its left and right entries are respectively one cyclic
`q*a`-window and one cyclic `q*b`-window of the factor orders.
-/
theorem cyclicWindow_balancedBlockOrder_left_start_scaled
    {P Q : Set α} {a b p q : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (hPQ : Disjoint P Q)
    (left : Fin (a * p) ≃ P)
    (right : Fin (b * p) ≃ Q)
    (i : Fin p) (u : Fin a) :
    cyclicWindow ((a + b) * q) (Nat.mul_pos (by omega) hp)
        (balancedBlockOrder hPQ left right)
        (blockPosition (a + b) p i (Fin.castAdd b u)) =
      cyclicWindow (b * q) (Nat.mul_pos hb hp) right
          (blockPosition b p i ⟨0, hb⟩) ∪
        cyclicWindow (a * q) (Nat.mul_pos ha hp) left
          (blockPosition a p i u) := by
  rw [cyclicWindow_mul_eq_iUnion_chunks
        (hn := Nat.mul_pos (by omega) hp) (hr := by omega)]
  rw [cyclicWindow_mul_eq_iUnion_chunks
        (hn := Nat.mul_pos hb hp) (hr := hb)]
  rw [cyclicWindow_mul_eq_iUnion_chunks
        (hn := Nat.mul_pos ha hp) (hr := ha)]
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨j, hx⟩
    have hG := cyclicIndex_blockPosition_mul
      (a + b) p (by omega) hp i (Fin.castAdd b u) j.val
    rw [hG] at hx
    have hchunk := cyclicWindow_balancedBlockOrder_left_start
      ha hb hp hPQ left right (cyclicIndex p hp i j.val) u
    rw [hchunk] at hx
    rcases hx with hxR | hxL
    · left
      refine ⟨j, ?_⟩
      have hR := cyclicIndex_blockPosition_mul
        b p hb hp i (⟨0, hb⟩ : Fin b) j.val
      rwa [hR]
    · right
      refine ⟨j, ?_⟩
      have hL := cyclicIndex_blockPosition_mul
        a p ha hp i u j.val
      rwa [hL]
  · rintro (⟨j, hxR⟩ | ⟨j, hxL⟩)
    · refine ⟨j, ?_⟩
      have hG := cyclicIndex_blockPosition_mul
        (a + b) p (by omega) hp i (Fin.castAdd b u) j.val
      have hR := cyclicIndex_blockPosition_mul
        b p hb hp i (⟨0, hb⟩ : Fin b) j.val
      rw [hR] at hxR
      rw [hG]
      rw [cyclicWindow_balancedBlockOrder_left_start
        ha hb hp hPQ left right (cyclicIndex p hp i j.val) u]
      exact Or.inl hxR
    · refine ⟨j, ?_⟩
      have hG := cyclicIndex_blockPosition_mul
        (a + b) p (by omega) hp i (Fin.castAdd b u) j.val
      have hL := cyclicIndex_blockPosition_mul
        a p ha hp i u j.val
      rw [hL] at hxL
      rw [hG]
      rw [cyclicWindow_balancedBlockOrder_left_start
        ha hb hp hPQ left right (cyclicIndex p hp i j.val) u]
      exact Or.inr hxL

/--
If a `q*(a+b)`-window starts in the right part of a period of
`(L^a R^b)^p`, its right and left entries are respectively one cyclic
`q*b`-window and one cyclic `q*a`-window of the factor orders.
-/
theorem cyclicWindow_balancedBlockOrder_right_start_scaled
    {P Q : Set α} {a b p q : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (hPQ : Disjoint P Q)
    (left : Fin (a * p) ≃ P)
    (right : Fin (b * p) ≃ Q)
    (i : Fin p) (v : Fin b) :
    cyclicWindow ((a + b) * q) (Nat.mul_pos (by omega) hp)
        (balancedBlockOrder hPQ left right)
        (blockPosition (a + b) p i (Fin.natAdd a v)) =
      cyclicWindow (b * q) (Nat.mul_pos hb hp) right
          (blockPosition b p i v) ∪
        cyclicWindow (a * q) (Nat.mul_pos ha hp) left
          (blockPosition a p (cyclicIndex p hp i 1) ⟨0, ha⟩) := by
  rw [cyclicWindow_mul_eq_iUnion_chunks
        (hn := Nat.mul_pos (by omega) hp) (hr := by omega)]
  rw [cyclicWindow_mul_eq_iUnion_chunks
        (hn := Nat.mul_pos hb hp) (hr := hb)]
  rw [cyclicWindow_mul_eq_iUnion_chunks
        (hn := Nat.mul_pos ha hp) (hr := ha)]
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨j, hx⟩
    have hG := cyclicIndex_blockPosition_mul
      (a + b) p (by omega) hp i (Fin.natAdd a v) j.val
    rw [hG] at hx
    have hchunk := cyclicWindow_balancedBlockOrder_right_start
      ha hb hp hPQ left right (cyclicIndex p hp i j.val) v
    rw [hchunk] at hx
    rcases hx with hxR | hxL
    · left
      refine ⟨j, ?_⟩
      have hR := cyclicIndex_blockPosition_mul
        b p hb hp i v j.val
      rwa [hR]
    · right
      refine ⟨j, ?_⟩
      have hL := cyclicIndex_blockPosition_mul
        a p ha hp (cyclicIndex p hp i 1) (⟨0, ha⟩ : Fin a) j.val
      rw [hL]
      have hcomm := cyclicIndex_add_commute p hp i 1 j.val
      rw [hcomm]
      exact hxL
  · rintro (⟨j, hxR⟩ | ⟨j, hxL⟩)
    · refine ⟨j, ?_⟩
      have hG := cyclicIndex_blockPosition_mul
        (a + b) p (by omega) hp i (Fin.natAdd a v) j.val
      have hR := cyclicIndex_blockPosition_mul
        b p hb hp i v j.val
      rw [hR] at hxR
      rw [hG]
      rw [cyclicWindow_balancedBlockOrder_right_start
        ha hb hp hPQ left right (cyclicIndex p hp i j.val) v]
      exact Or.inl hxR
    · refine ⟨j, ?_⟩
      have hG := cyclicIndex_blockPosition_mul
        (a + b) p (by omega) hp i (Fin.natAdd a v) j.val
      have hL := cyclicIndex_blockPosition_mul
        a p ha hp (cyclicIndex p hp i 1) (⟨0, ha⟩ : Fin a) j.val
      rw [hL] at hxL
      have hcomm := cyclicIndex_add_commute p hp i 1 j.val
      rw [hcomm] at hxL
      rw [hG]
      rw [cyclicWindow_balancedBlockOrder_right_start
        ha hb hp hPQ left right (cyclicIndex p hp i j.val) v]
      exact Or.inr hxL

/--
Every cyclic `q*(a+b)`-window in `(L^a R^b)^p` decomposes into one cyclic
`q*b`-window of the right factor and one cyclic `q*a`-window of the left.
This is purely combinatorial: it contains no matroid or density hypothesis.
-/
theorem cyclicWindow_balancedBlockOrder_scaled_decomposition
    {P Q : Set α} {a b p q : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (hPQ : Disjoint P Q)
    (left : Fin (a * p) ≃ P)
    (right : Fin (b * p) ≃ Q)
    (z : Fin ((a + b) * p)) :
    ∃ iL : Fin (a * p), ∃ iR : Fin (b * p),
      cyclicWindow ((a + b) * q) (Nat.mul_pos (by omega) hp)
          (balancedBlockOrder hPQ left right) z =
        cyclicWindow (b * q) (Nat.mul_pos hb hp) right iR ∪
          cyclicWindow (a * q) (Nat.mul_pos ha hp) left iL := by
  let w : Fin p × Fin (a + b) :=
    (blockPositionEquiv (a + b) p).symm z
  let i : Fin p := w.1
  let d : Fin (a + b) := w.2
  have hz : blockPosition (a + b) p i d = z := by
    change blockPositionEquiv (a + b) p (i, d) = z
    simpa [i, d, w] using
      (blockPositionEquiv (a + b) p).apply_symm_apply z
  by_cases hd : d.val < a
  · let u : Fin a := ⟨d.val, hd⟩
    have hdu : d = Fin.castAdd b u := by
      apply Fin.ext
      rfl
    refine ⟨blockPosition a p i u,
      blockPosition b p i ⟨0, hb⟩, ?_⟩
    have hstart :
        z = blockPosition (a + b) p i (Fin.castAdd b u) := by
      calc
        z = blockPosition (a + b) p i d := hz.symm
        _ = blockPosition (a + b) p i (Fin.castAdd b u) := by
          rw [hdu]
    calc
      cyclicWindow ((a + b) * q) (Nat.mul_pos (by omega) hp)
          (balancedBlockOrder hPQ left right) z =
        cyclicWindow ((a + b) * q) (Nat.mul_pos (by omega) hp)
          (balancedBlockOrder hPQ left right)
          (blockPosition (a + b) p i (Fin.castAdd b u)) := by
            exact congrArg
              (fun t : Fin ((a + b) * p) =>
                cyclicWindow ((a + b) * q) (Nat.mul_pos (by omega) hp)
                  (balancedBlockOrder hPQ left right) t)
              hstart
      _ = cyclicWindow (b * q) (Nat.mul_pos hb hp) right
            (blockPosition b p i ⟨0, hb⟩) ∪
          cyclicWindow (a * q) (Nat.mul_pos ha hp) left
            (blockPosition a p i u) :=
        cyclicWindow_balancedBlockOrder_left_start_scaled
          ha hb hp hPQ left right i u
  · have had : a ≤ d.val := by omega
    let v : Fin b := ⟨d.val - a, by omega⟩
    have hdv : d = Fin.natAdd a v := by
      apply Fin.ext
      change d.val = a + (d.val - a)
      omega
    refine ⟨blockPosition a p (cyclicIndex p hp i 1) ⟨0, ha⟩,
      blockPosition b p i v, ?_⟩
    have hstart :
        z = blockPosition (a + b) p i (Fin.natAdd a v) := by
      calc
        z = blockPosition (a + b) p i d := hz.symm
        _ = blockPosition (a + b) p i (Fin.natAdd a v) := by
          rw [hdv]
    calc
      cyclicWindow ((a + b) * q) (Nat.mul_pos (by omega) hp)
          (balancedBlockOrder hPQ left right) z =
        cyclicWindow ((a + b) * q) (Nat.mul_pos (by omega) hp)
          (balancedBlockOrder hPQ left right)
          (blockPosition (a + b) p i (Fin.natAdd a v)) := by
            exact congrArg
              (fun t : Fin ((a + b) * p) =>
                cyclicWindow ((a + b) * q) (Nat.mul_pos (by omega) hp)
                  (balancedBlockOrder hPQ left right) t)
              hstart
      _ = cyclicWindow (b * q) (Nat.mul_pos hb hp) right
            (blockPosition b p i v) ∪
          cyclicWindow (a * q) (Nat.mul_pos ha hp) left
            (blockPosition a p (cyclicIndex p hp i 1) ⟨0, ha⟩) :=
        cyclicWindow_balancedBlockOrder_right_start_scaled
          ha hb hp hPQ left right i v

end

end HigherRankKUM
