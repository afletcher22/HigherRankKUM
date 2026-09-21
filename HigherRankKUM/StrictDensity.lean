import HigherRankKUM.RationalDensity

namespace HigherRankKUM

open Set

variable {α : Type*}

/--
Strict uniform density at the rational ratio `p/q`, imposed on nonempty
proper ground-set subsets:

`q * |X| < p * r(X)`.

The ambient ground-set equality is deliberately not built into this predicate;
callers that use it as a KUM density hypothesis should separately supply the
rank and ground-set cardinality.
-/
def StrictlyUniformlyDenseRatio (M : Matroid α) (p q : ℕ) : Prop :=
  ∀ X : Set α, X ⊆ M.E → X.Nonempty → X ≠ M.E →
    (q : ℕ∞) * X.encard < (p : ℕ∞) * M.eRk X

end HigherRankKUM
