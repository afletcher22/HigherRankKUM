import HigherRankKUM.VHT.Theorem21
import HigherRankKUM.LowRank.RankThree

/-!
# Prime rank: divisible KUM suffices

At a prime rank `p`, every ground-set size is either coprime to `p` or a multiple of it. The
coprime sizes are settled by van den Heuvel–Thomassé (`VHT.solvesKUMAtRankSize_of_coprime`), so
full KUM at rank `p` follows from divisible KUM at rank `p`.

Consequences:

* full rank-3 KUM, from the vendored divisible rank-3 theorem;
* odd-size rank-2 KUM, which is coprime.
-/

namespace HigherRankKUM

variable {α : Type*}

/-- At a prime rank, divisible KUM implies full KUM. -/
theorem solvesKUMAtRank_of_prime {p : ℕ} (hp : p.Prime) (hdiv : SolvesDivisibleKUMAtRank α p) :
    SolvesKUMAtRank α p := by
  intro n
  rcases Nat.coprime_or_dvd_of_prime hp n with hcop | ⟨k, rfl⟩
  · exact VHT.solvesKUMAtRankSize_of_coprime hcop
  · intro N hr hn hE hRank hEcard hDense
    have hk : 0 < k := Nat.pos_of_mul_pos_left hn
    have hDense' : UniformlyDense N k := by
      intro X hX
      have h := hDense X hX
      push_cast at h
      rw [mul_assoc] at h
      exact (ENat.mul_le_mul_left_iff (by exact_mod_cast hp.ne_zero) (by simp)).1 h
    exact hdiv N k hr hk hE hRank hEcard hDense'

/-- **Rank-3 KUM**, at every ground-set size. -/
theorem solvesKUMAtRank_three : SolvesKUMAtRank α 3 :=
  solvesKUMAtRank_of_prime Nat.prime_three solvesDivisibleKUMAtRank_three

/-- **Rank-2 KUM at odd sizes.** -/
theorem solvesKUMAtRankSize_two_odd (k : ℕ) : SolvesKUMAtRankSize α 2 (2 * k + 1) :=
  VHT.solvesKUMAtRankSize_of_coprime (Nat.coprime_two_left.2 (odd_two_mul_add_one k))

end HigherRankKUM
