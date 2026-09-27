# Human proofs of the local lemmas EVEN and ODD (rank 4, 12 elements)

**Status.** These are complete human proofs. They use only closure, exchange, submodularity (in
the form "two distinct planes meet in a line"), rank-2 contractions and the Greene–Magnanti
exchange theorem. Every intermediate claim was also confirmed by SAT (Appendix). No step of the
proof depends on SAT.

**Shape of the argument.**

1. **Part A (window analysis, no matroid geometry).** Tightness turns each window condition into
   a non-parallelism between a pair and a pair in a rank-2 contraction. This gives the following
   for a valid split (P, Q):
   * EVEN fails exactly when (P, Q) is **P-crossed** or **Q-crossed**.
   * ODD fails exactly when all four matchings exist and exactly one of the two crossings holds.

   So a valid split that is **neither P-crossed nor Q-crossed is good for both lemmas**. ODD needs
   no separate geometric argument.
2. **Part B (8 elements: S, A₀, A₁; no tightness).** *Main Lemma:* some valid split is neither
   P-crossed nor Q-crossed. The proof has three ingredients:
   * **Greene–Magnanti** gives a valid split.
   * **Lemma F1** (the one-swap cover of the P-only lemma): if the split is P-crossed, a split
     obtained by swapping one element of P with one of Q is valid and not P-crossed.
   * **Lemma F2** (five lines): no one-swap of a P-crossed split is Q-crossed.

   The Q-crossed case is the mirror image.

So EVEN and ODD follow from the P-only cover theorem plus the short Lemma F2 and the parity count
of Step 5. Lemma F1 is Theorem 3 of `XP_LOCAL_LEMMA_PQ.md`. For self-containment, a short
independent proof is given in Step 9.

---

## 0. Conventions and standard facts

M is a matroid of rank 4 with rank function r and closure cl. We write X + e for X ∪ {e}, and
cl(e₁, …, e_k) for cl({e₁, …, e_k}). A *flat* is a closed set, a *line* is a flat of rank 2, and a
*plane* is a flat of rank 3. A 4-set is a basis if and only if it is independent. Subsets of
independent sets are independent.

* **(M1)** If I is independent, then I + e is independent if and only if e ∉ cl(I). If F is a flat,
  X ⊆ F and r(X) = r(F), then cl(X) = F. In particular, if I ⊆ F is independent with |I| = r(F),
  then F = cl(I). An intersection of flats is a flat.
* **(M2) Exchange** (MacLane–Steinitz). If e ∈ cl(X + f) and e ∉ cl(X), then f ∈ cl(X + e).
  For X = ∅: if e is not a loop and e ∈ cl(f), then f ∈ cl(e).
* **(M3) Two flats of the same rank.** Let F ≠ G be flats of rank k. Then r(F ∩ G) ≤ k − 1. If
  F ∩ G contains an independent set I with |I| = k − 1, then F ∩ G = cl(I).
  *Proof.* F ∩ G is a flat. If its rank were k, (M1) would give F ∩ G = F and F ∩ G = G.
  If I ⊆ F ∩ G, then cl(I) ⊆ F ∩ G, and the two ranks agree, so (M1) applies. ∎
  We use two cases:
  * two distinct planes that both contain an independent pair {e, f} meet in the line cl(e, f);
  * two distinct lines that both contain a non-loop e meet in cl(e).
* **(M4) Rank-2 contractions.** Let C be an independent 2-set. Then M/C has rank 2, and for a
  2-set {s, t} disjoint from C: {s, t} is a basis of M/C ⟺ C ∪ {s, t} is a basis of M. The loops
  of M/C are the elements of cl(C). For non-loops s and t, write s ∥_C t ("s and t are parallel
  in M/C", allowing s = t) when the following equivalent conditions hold:
  * C ∪ {s, t} is dependent;
  * t ∈ cl(C + s);
  * cl(C + s) = cl(C + t).

  The equivalences follow from (M1). By the last form, ∥_C is an equivalence relation on the
  non-loops of M/C. Two non-loops s ≠ t form a basis of M/C if and only if s ∦_C t.
* **(M5) Matchings.** Let X and Y be 2-sets that are both bases of M/C. The elements of X are
  non-loops and not parallel to each other, so by transitivity each element of Y is ∥_C to at most
  one element of X, and vice versa. So
  E_C(X, Y) := {(s, t) ∈ X × Y : s ∥_C t}
  is a *matching*: no two of its pairs share a coordinate. In particular |E_C(X, Y)| ≤ 2.
  If |E_C(X, Y)| = 2, it is the graph of a bijection X → Y. We call this bijection the
  **matching μ_C(X → Y)** and say that it *exists*.
  Two different bijections between 2-sets differ at both points.
* **(GM) Greene–Magnanti** (multiple symmetric exchange, two blocks). If B, B′ are bases and
  B = X₁ ⊔ X₂, then B′ = Y₁ ⊔ Y₂ with (B ∖ X₁) ∪ Y₁ and (B ∖ X₂) ∪ Y₂ both bases (so |Yᵢ| = |Xᵢ|).

---

## 1. The statement

There are twelve distinct elements. S = {s₀, s₁, s₂, s₃} is a basis. The pairs are
A₋₁ = (x, x̄), A₀ = (a, ā), A₁ = (b, b̄) and A₂ = (y, ȳ), each written as (first, last).

**Hypotheses.** Only the following are used:

* **(h1)** S is a basis.
* **(h2)** A₀ ∪ A₁ is a basis.
* **(h3)** A₋₁ ∪ A₀ and A₁ ∪ A₂ are bases.
* **(t−1)** tightness of R₋₁: {x, a, ā, b} and {x̄, a, ā, b̄} are *not* bases.
* **(t0)** tightness of R₀: {a, b, b̄, y} and {ā, b, b̄, ȳ} are *not* bases.

The other hypotheses of the task follow or are not needed:

* {x̄, a, ā, b}, {ā, b, b̄, y}, {x, a, ā, b̄} and {a, b, b̄, ȳ} are bases;
* x ∦ x̄ in M/A₀.

**Flips.** For a 2-set X with a reference orientation (x₀, x₁) and a bit o, let X^(o) be the
orientation (x_o, x_{o+1}), with indices mod 2. So first X^(o) = x_o and last X^(o) = x_{o+1}.
Use the references P = (p₀, p₁), Q = (q₀, q₁), A₀ = (a₀, a₁) = (a, ā) and
A₁ = (b₀, b₁) = (b, b̄). The oriented split is P′ = P^(o_P) and Q′ = Q^(o_Q). The flipped pairs are:

| lemma | A′₋₁ | A′₀ | A′₁ | A′₂ |
|---|---|---|---|---|
| **ODD** | A₋₁^(e₁) | A₀^(e₂) | A₁^(e₂) | A₂^(e₁) |
| **EVEN** | A₋₁^(e₁) | A₀^(e₂) | A₁^(e₁) | A₂^(e₂) |

**Windows.**

* Wa = {last A′₋₁} ∪ A₀ ∪ {first P′}
* Wb = {last A′₀} ∪ P ∪ {first Q′}
* Wc = {last P′} ∪ Q ∪ {first A′₁}
* Wd = {last Q′} ∪ A₁ ∪ {first A′₂}

An ordered split (P, Q) of S (|P| = |Q| = 2) is **valid** if A₀ ∪ P and Q ∪ A₁ are bases.

**Lemma ODD / Lemma EVEN.** Some valid split and some bits o_P, o_Q, e₁, e₂ make Wa, Wb, Wc and Wd
all bases, with the flips of the respective row.

---

# Part A: from windows to crossings

### Step 1 (each window is a non-parallelism in a rank-2 contraction)

Let (P, Q) be valid. The following 2-sets are bases of the following rank-2 contractions, by (M4):

| contraction | 2-sets that are bases | reason |
|---|---|---|
| M/A₀ | A₋₁, P, A₁ | (h3), validity, (h2) |
| M/P | A₀, Q | validity, (h1) |
| M/Q | P, A₁ | (h1), validity |
| M/A₁ | Q, A₀, A₂ | validity, (h2), (h3) |

So every element named below is a non-loop of the contraction in question. The twelve elements
are distinct, so by (M4):

* Wa is a basis ⟺ last A′₋₁ ∦_{A₀} first P′;
* Wb is a basis ⟺ last A′₀ ∦_P first Q′;
* Wc is a basis ⟺ last P′ ∦_Q first A′₁;
* Wd is a basis ⟺ last Q′ ∦_{A₁} first A′₂.

### Step 2 (tightness replaces A₋₁ by A₁ and A₂ by A₀)

The elements x, x̄, b and b̄ are non-loops of M/A₀ by Step 1. So (t−1) and (M4) give **x ∥_{A₀} b**
and **x̄ ∥_{A₀} b̄**. In the same way (t0) gives **a ∥_{A₁} y** and **ā ∥_{A₁} ȳ**.

The bijection x ↦ b, x̄ ↦ b̄ sends last A₋₁^(e) to last A₁^(e), for either value of e. Since ∥_{A₀}
is an equivalence relation, last A₋₁^(e) ∥_{A₀} t ⟺ last A₁^(e) ∥_{A₀} t for every non-loop t. In
the same way, first A₂^(e) ∥_{A₁} t ⟺ first A₀^(e) ∥_{A₁} t.

In both lemmas A₋₁ carries the flip e₁ and A₀ the flip e₂. So Step 1 becomes:

* **(Wa)** (p_{o_P}, b_{e₁+1}) ∉ E_{A₀}(P, A₁)
* **(Wb)** (q_{o_Q}, a_{e₂+1}) ∉ E_P(Q, A₀)
* **(Wc)** (p_{o_P+1}, b_h) ∉ E_Q(P, A₁)
* **(Wd)** (q_{o_Q+1}, a_k) ∉ E_{A₁}(Q, A₀)

Here (h, k) = (e₁, e₂) for EVEN and (h, k) = (e₂, e₁) for ODD. (For Wb, use that
q ∥_P a ⟺ a ∥_P q.)

### Step 3 (matchings and crossings)

For a valid split, the four sets E above are matchings by (M5) and Step 1. Let

* μ₀ := μ_{A₀}(P → A₁)
* μ_Q := μ_Q(P → A₁)
* ν_P := μ_P(Q → A₀)
* ν₁ := μ_{A₁}(Q → A₀)

whenever they exist.

**Definition.** A valid split (P, Q) is:

* **P-crossed** if μ₀ and μ_Q both exist and μ₀ ≠ μ_Q;
* **Q-crossed** if ν_P and ν₁ both exist and ν_P ≠ ν₁.

Unfolded, these read as follows.

* P-crossed means P = {u, v} with u ∥_{A₀} b, v ∥_{A₀} b̄, u ∥_Q b̄ and v ∥_Q b. By (M4) this is
  u ∈ cl(A₀ + b), v ∈ cl(A₀ + b̄), b̄ ∈ cl(Q + u) and b ∈ cl(Q + v). This is "crossed" in
  `crossed.py` and in `handproof_pq`.
* Q-crossed means Q = {w, z} with w ∥_P a, z ∥_P ā, w ∥_{A₁} ā and z ∥_{A₁} a. This is
  "mirror-crossed" in `handproof_pq` §3.

Neither notion depends on the orientations of any pair.

For fixed variables, each of the four constraints is a map {0,1}² → X × Y. For example, Wa is
(o_P, e₁) ↦ (p_{o_P}, b_{e₁+1}). This map is a bijection, and each coordinate of the image depends
on only one of the two bits. So each constraint forbids a set of bit-pairs that is a matching:
for each value of either bit, at most one value of the other bit is forbidden. The constraint
forbids exactly two bit-pairs (call it **rigid**) if and only if the corresponding matching μ₀, μ_Q,
ν_P or ν₁ exists.

### Step 4 (EVEN: two independent 2-cycles)

In EVEN, the bits (o_P, e₁) occur only in Wa and Wc, and (o_Q, e₂) occur only in Wb and Wd.

**Claim 4.1.** Some (o_P, e₁) satisfies Wa and Wc if and only if (P, Q) is not P-crossed.

*Proof.* The map (o_P, e₁) ↦ (s, t) := (p_{o_P}, b_{e₁+1}) is a bijection onto P × A₁. Under it,
Wc concerns (p_{o_P+1}, b_{e₁}) = (s̄, t̄), where the bar denotes the other element of the pair.
So all four bit-pairs fail if and only if every (s, t) ∈ P × A₁ lies in E ∪ E″, where

* E = E_{A₀}(P, A₁);
* E″ = {(s, t) : (s̄, t̄) ∈ E_Q(P, A₁)}.

E is a matching, and so is E″, because (s, t) ↦ (s̄, t̄) preserves "sharing a coordinate".
So |E|, |E″| ≤ 2, and the four pairs are covered if and only if |E| = |E″| = 2 and E ∩ E″ = ∅.

* |E| = 2 means μ₀ exists and E = graph μ₀.
* |E″| = 2 means μ_Q exists. Then E″ = {(s, t) : μ_Q(s̄) = t̄} = graph μ_Q, since a bijection
  between 2-sets maps s̄ to the complement of the image of s.

Two perfect matchings of K₂,₂ are equal or disjoint. So E ∩ E″ = ∅ ⟺ μ₀ ≠ μ_Q. ∎

**Claim 4.2.** Some (o_Q, e₂) satisfies Wb and Wd if and only if (P, Q) is not Q-crossed.

*Proof.* The same argument with (o_Q, e₂) ↦ (q_{o_Q}, a_{e₂+1}), E = E_P(Q, A₀) and
E″ from E_{A₁}(Q, A₀). In EVEN, Wd concerns (q_{o_Q+1}, a_{e₂}). ∎

**So EVEN holds for a valid (P, Q) if and only if (P, Q) is neither P-crossed nor Q-crossed.**

### Step 5 (ODD: one 4-cycle with a parity)

In ODD the constraints form the 4-cycle e₁ –Wa– o_P –Wc– e₂ –Wb– o_Q –Wd– e₁.

**Claim 5.1.** If some constraint is not rigid, all four can be satisfied.

*Proof.* Say constraint K is not rigid, and let its forbidden bit-pairs be at most {(α, β)}, on its
variables (X₁, X₂). Deleting K leaves a path of three constraints from X₁ to X₂ through the other
two variables.

Set X₁ := 1 − α (or X₁ := 0 if K forbids nothing). Then walk along the path. Each constraint
forbids at most one value of the next variable given the current one (Step 3), so a value can
always be chosen. K is satisfied because X₁ ≠ α. ∎

**Claim 5.2.** If all four are rigid, they can be satisfied if and only if P-crossed and
Q-crossed are either both true or both false.

*Proof.* Write each bijection in the reference indices: μ₀(p_i) = b_{i+π₀}, μ_Q(p_i) = b_{i+π_Q},
ν_P(q_i) = a_{i+π′_P} and ν₁(q_i) = a_{i+π′₁}, with π's in ℤ/2. By Step 2:

* Wa forbids (o_P, e₁) iff μ₀(p_{o_P}) = b_{e₁+1}, i.e. iff o_P + π₀ = e₁ + 1. So Wa ⟺
  o_P + e₁ = π₀.
* Wc forbids iff μ_Q(p_{o_P+1}) = b_{e₂}. So Wc ⟺ o_P + e₂ = π_Q.
* Wb forbids iff ν_P(q_{o_Q}) = a_{e₂+1}. So Wb ⟺ o_Q + e₂ = π′_P.
* Wd forbids iff ν₁(q_{o_Q+1}) = a_{e₁}. So Wd ⟺ o_Q + e₁ = π′₁.

The four left-hand sides sum to 0 over ℤ/2. So solvability requires π₀ + π_Q + π′_P + π′₁ = 0.
Conversely, if the sum is 0, the following is a solution:

* e₁ = 0;
* o_P = π₀;
* e₂ = π₀ + π_Q;
* o_Q = e₂ + π′_P.

Then o_Q + e₁ = π₀ + π_Q + π′_P = π′₁.

Finally, π₀ = π_Q ⟺ μ₀ = μ_Q ⟺ not P-crossed, and π′_P = π′₁ ⟺ not Q-crossed. ∎

**So ODD holds for a valid (P, Q) unless all four matchings exist and exactly one of P-crossed and
Q-crossed holds.**

### Step 6 (consequence)

By Steps 4 and 5, **a valid split that is neither P-crossed nor Q-crossed satisfies the EVEN
windows and the ODD windows** for suitable bits. Both lemmas therefore follow from the Main
Lemma of Part B. Part B involves only the 8 elements S ∪ A₀ ∪ A₁ and the hypotheses (h1) and (h2).

---

# Part B: the 8-element Main Lemma

**Main Lemma.** Let M have rank 4, and let S, A₀ and A₁ be pairwise disjoint, with |A₀| = |A₁| = 2,
S a basis and A₀ ∪ A₁ a basis. Then some valid split (P, Q) of S is neither P-crossed nor
Q-crossed.

### Step 7 (mirror symmetry)

Let the mirrored configuration have the same M and S, with A₀* := A₁ and A₁* := A₀. Map a split
(P, Q) to (P*, Q*) := (Q, P).

* **Validity is preserved.** A₀* ∪ P* = A₁ ∪ Q and Q* ∪ A₁* = P ∪ A₀.
* **P*-crossed in the mirror ⟺ Q-crossed originally.** In the mirror, μ_{A₀*}(P* → A₁*) =
  μ_{A₁}(Q → A₀) = ν₁ and μ_{Q*}(P* → A₁*) = μ_P(Q → A₀) = ν_P.
* **Q*-crossed in the mirror ⟺ P-crossed originally**, by the same computation.

The hypotheses of the Main Lemma are invariant under the mirror.

### Step 8 (standing hypotheses: a P-crossed valid split)

In Steps 8–10, (P, Q) is valid and P-crossed. Label P = {u, v} with μ₀(u) = b. Then μ₀(v) = b̄,
and since μ_Q ≠ μ₀, also μ_Q(u) = b̄ and μ_Q(v) = b. Write Q = {w, z}. Let

* H := cl(a, ā, b)
* H̄ := cl(a, ā, b̄)

**Independent sets used.** All subsets of the following four bases:

* B = {a, ā, b, b̄};
* S = {u, v, w, z};
* A₀ ∪ P = {a, ā, u, v};
* Q ∪ A₁ = {w, z, b, b̄}.

By (M4), the crossing gives:

* **(X1)** cl(a, ā, u) = H, so u ∈ H.
* **(X2)** cl(a, ā, v) = H̄, so v ∈ H̄.
* **(X3)** cl(u, w, z) = cl(w, z, b̄) =: G, so b̄ ∈ G.
* **(X4)** cl(v, w, z) = cl(w, z, b) =: G′, so b ∈ G′.

Two consequences:

* **(D1)** b̄ ∉ H and b ∉ H̄, because B is independent. Hence H ≠ H̄, and by (M3)
  H ∩ H̄ = cl(a, ā).
* **(D2)** u, v ∉ cl(a, ā), because A₀ ∪ P is independent.

The one-swap splits keeping u in P are:

* X_w := ({u, w}, {v, z})
* X_z := ({u, z}, {v, w})

All hypotheses are symmetric under renaming w ↔ z, which swaps X_w and X_z. We call this the
**twin** symmetry.

### Step 9 (Lemma F1: the one-swap cover, = Theorem 3 of handproof_pq)

**9.0 (validity).** X_w is valid ⟺ w ∉ H and v ∉ cl(z, b, b̄).
*Proof.* {a, ā, u} is independent with closure H (X1), and {z, b, b̄} is independent. Apply (M1). ∎

**9.1.** w and z are not both in H.
*Proof.* Otherwise G = cl(u, w, z) ⊆ H by (X1). Since b̄ ∈ G by (X3), this contradicts (D1). ∎

**9.2.** If v ∈ cl(w, b, b̄), then v ∈ cl(w, b), w ∉ H and w ∉ H̄.

*Proof.* cl(w, b, b̄) and G′ = cl(w, z, b) are planes. They are distinct, because z ∉ cl(w, b, b̄)
(Q ∪ A₁ is independent). Both contain the independent pair {w, b}. By (X4) v lies in both, so
(M3) gives v ∈ cl(w, b).

* If w ∈ H, then cl(w, b) ⊆ H, so v ∈ H ∩ H̄ = cl(a, ā), contradicting (D2).
* If w ∈ H̄: v ∉ cl(w) (S is independent), so (M2) gives b ∈ cl(v, w) ⊆ H̄, contradicting (D1). ∎

The twin statement 9.2′ holds for z.

**9.3.** v ∈ cl(w, b, b̄) and v ∈ cl(z, b, b̄) do not both hold.

*Proof.* Otherwise 9.2 and 9.2′ give v ∈ cl(w, b) ∩ cl(z, b). These lines are distinct, since
{w, z, b} is independent, and both contain b. So (M3) gives v ∈ cl(b). Since v is not a loop,
(M2) gives b ∈ cl(v) ⊆ H̄, contradicting (D1). ∎

**9.4.** X_w or X_z is valid.

*Proof.* If both are invalid, 9.0 gives (w ∈ H or v ∈ cl(z, b, b̄)) and (z ∈ H or v ∈ cl(w, b, b̄)).
The four combinations are excluded as follows:

* w ∈ H and z ∈ H: 9.1;
* w ∈ H and v ∈ cl(w, b, b̄): 9.2;
* v ∈ cl(z, b, b̄) and z ∈ H: 9.2′;
* v ∈ cl(z, b, b̄) and v ∈ cl(w, b, b̄): 9.3. ∎

**9.5.** If X_w is valid and P-crossed, then w ∈ H̄ and u ∈ cl(z, b̄).

*Proof.* Let P′ = {u, w} and Q′ = {v, z}.

* The matching μ_{A₀}(P′ → A₁) exists and sends u ↦ b, by (X1). So it sends w ↦ b̄, which means
  w ∈ cl(A₀ + b̄) = H̄.
* The matching μ_{Q′}(P′ → A₁) exists and differs from it, so it sends u ↦ b̄. That means
  u ∈ cl(v, z, b̄).

The planes cl(v, z, b̄) and G = cl(w, z, b̄) are distinct:

* cl(v, z, b̄) is a plane because Q′ ∪ A₁ is a basis (X_w is valid);
* if the two were equal, then v ∈ G = cl(u, w, z), contradicting the independence of S.

Both planes contain the independent pair {z, b̄}, and u lies in both (X3). So (M3) gives
u ∈ cl(z, b̄). ∎

The twin statement 9.5′ is: if X_z is valid and P-crossed, then z ∈ H̄ and u ∈ cl(w, b̄).

**9.6.** X_w and X_z are not both valid and P-crossed.
*Proof.* Otherwise w, z ∈ H̄ (9.5 and 9.5′) and v ∈ H̄ (X2). Then G′ = cl(v, w, z) ⊆ H̄, and
b ∈ G′ by (X4), contradicting (D1). ∎

**9.7.** If X_w is valid and P-crossed, then X_z is valid.

*Proof.* If not, 9.0 gives z ∈ H or v ∈ cl(w, b, b̄).

* If z ∈ H: by 9.5, u ∈ cl(z, b̄), and u ∉ cl(z). So (M2) gives b̄ ∈ cl(u, z) ⊆ H (X1),
  contradicting (D1).
* If v ∈ cl(w, b, b̄): 9.2 gives w ∉ H̄, contradicting 9.5. ∎

The twin statement 9.7′ holds as well.

**Lemma F1.** X_w or X_z is valid and not P-crossed.

*Proof.* By 9.4, and using the twin symmetry, we may assume X_w is valid. If X_w is not
P-crossed, we are done. Otherwise X_z is valid by 9.7 and not P-crossed by 9.6. ∎

### Step 10 (Lemma F2: one-swaps of a P-crossed split are not Q-crossed)

**Lemma F2.** If X_w is valid, then X_w is not Q-crossed. By the twin symmetry, the same holds
for X_z.

*Proof.* Let P′ = {u, w} and Q′ = {v, z}, and suppose ν′_{P′} := μ_{P′}(Q′ → A₀) and
ν′₁ := μ_{A₁}(Q′ → A₀) exist and differ. Let t := ν′₁(v) ∈ A₀. The two bijections differ at v, so
ν′_{P′}(z) = t. Hence:

* v ∥_{A₁} t, i.e. v ∈ cl(t, b, b̄);
* z ∥_{P′} t, i.e. t ∈ cl(u, w, z) = G.

The planes cl(t, b, b̄) and H̄ are distinct, since b ∉ H̄ (D1). Both contain the independent pair
{t, b̄} ⊆ B, and v lies in both (X2). So (M3) gives v ∈ cl(t, b̄).

But t ∈ G and b̄ ∈ G (X3), so v ∈ cl(t, b̄) ⊆ G = cl(u, w, z). This contradicts the independence
of S. ∎

(By the symmetry u ↔ v, b ↔ b̄ of Step 8, the same holds for the other two one-swaps, ({v, w}, {u, z})
and ({v, z}, {u, w}). This is not needed.)

### Step 11 (proof of the Main Lemma)

Apply (GM) with B = A₀ ∪ A₁, X₁ = A₁, X₂ = A₀ and B′ = S. It gives a partition S = P ⊔ Q with
A₀ ∪ P and A₁ ∪ Q bases. So (P, Q) is a valid split. There are three cases.

* **Neither P-crossed nor Q-crossed.** Done.
* **P-crossed.** Label it as in Step 8. Lemma F1 gives X ∈ {X_w, X_z} that is valid and not
  P-crossed. Lemma F2 shows that X is not Q-crossed. Done.
* **Q-crossed.** By Step 7, (Q, P) is a valid, P*-crossed split of the mirrored configuration.
  The previous case, applied there, gives a valid split (P₁*, Q₁*) of the mirror that is neither
  P*-crossed nor Q*-crossed. By Step 7 again, (Q₁*, P₁*) is a valid split of the original
  configuration that is neither Q-crossed nor P-crossed. ∎

### Step 12 (proof of Lemmas EVEN and ODD)

The 12-element hypotheses contain (h1) and (h2). So the Main Lemma gives a valid split (P, Q)
that is neither P-crossed nor Q-crossed. By Step 6 (that is, Claims 4.1, 4.2, 5.1 and 5.2), some
o_P, o_Q, e₁, e₂ make Wa, Wb, Wc and Wd bases, in EVEN and in ODD. ∎

---

## Remarks

1. **Length.**
   * Part A (Steps 1–6) is about one page. It is bookkeeping: two 2×2 matching claims and one
     ℤ/2 parity count on a 4-cycle.
   * Part B (Steps 7–11) is about one and a half pages. Lemma F1 is eight claims of one to four
     lines each. Lemma F2 is five lines. The mirror is a three-line table.

   The only case analyses are the four-way split in 9.4, the two-way split in 9.7 and the two
   cases of 5.1/5.2.
2. **Where tightness enters.** Tightness is used only in Step 2, to identify last A′₋₁ with
   last A_1^(e₁) in M/A₀ and first A′₂ with first A₀^(·) in M/A₁. Without it, Wa and Wd would
   involve x and y independently of the other two constraints, and both lemmas are false
   (known SAT result).
3. **The two flip patterns differ only in Step 5 versus Step 4.** Crossing has the same meaning in
   both. That is why one split serves both lemmas.
4. **Exact failure sets.** For a valid split:
   * EVEN fails ⟺ P-crossed or Q-crossed.
   * ODD fails ⟺ μ₀, μ_Q, ν_P and ν₁ all exist and exactly one of P-crossed, Q-crossed holds.
5. **Explicit recipe.**
   * Take the Greene–Magnanti split.
   * If it is P-crossed, keep in P the element u with u ∥_{A₀} b, and swap the other one with w
     or with z. One of the two results works.
   * If it is Q-crossed, do the mirror: keep in Q the element w with w ∥_{A₁} a, and swap the
     other one with an element of P.
6. **Relation to `handproof_pq`.** Lemma F1 is its Theorem 3 (their Lemma F is our 9.5; their
   Lemma A is our 9.1 together with 9.6; their Lemmas B, C and E(a) cover our 9.2 and 9.3). The
   P-only and Q-only lemmas are the "P-part" (Claim 4.1) and "Q-part" (Claim 4.2) of EVEN, and
   they need only (t−1) or only (t0) respectively. Beyond P-only, EVEN and ODD need exactly three
   things: Lemma F2, the mirror argument of Step 11, and the parity count of Step 5.
7. **Gaps.** None known. Points to watch:
   * the twelve elements must be distinct, which is used in Step 1 and wherever S is disjoint
     from A₀ ∪ A₁;
   * validity must hold for the one-swap split before crossing is even defined, which F1
     provides.

---

## Appendix: SAT cross-checks (not used by the proof)

The scripts are in `experiments/rank4_heavy_flat_splice/handproof_oe/`. They use the full rank-function encoding of `local_xp.py`
(all rank axioms, CaDiCaL 1.9.5 via pysat).

* **`verify12.py`** (12 elements; hypotheses of `local_xp.py` with `tightm1 tight0`). For every
  one of the 6 ordered splits and both modes:
  * "valid ∧ no bits work ∧ ¬bad" is UNSAT;
  * "valid ∧ some bits work ∧ bad" is UNSAT;
  * "valid ∧ not crossed ∧ no bits work" is UNSAT.

  Here *bad* is the Step 4 / Step 5 failure set. So Steps 1–6 are confirmed in both directions.
  Controls confirm that failing, P-crossed and Q-crossed valid splits all occur (SAT).
* **`check8.py`** (8 elements, (h1) and (h2) only). Each of "every valid split is P-crossed",
  "… Q-crossed", "… P- or Q-crossed" and "… ODD-bad" is UNSAT.
* **`verify8.py`** (8 elements, with the standing hypotheses of Step 8). The following are
  confirmed, with controls SAT:
  * claims 9.0–9.7 and their twins;
  * Lemma F1;
  * Lemma F2, for all four one-swap splits;
  * the Main Lemma.
* **`cover8.py`**. The minimal covers are all of size 2 and consist of one-swap splits:
  * for EVEN from a P-crossed split: {X_w, X_z} and its u ↔ v twin;
  * for EVEN from a Q-crossed split: the mirror of that;
  * for ODD: four covers, including the "complementary" pairs ({u,w},{v,z}) and ({v,z},{u,w}).
* **`backbone8.py Pcross`**: every one-swap of a P-crossed valid split is forced to be not
  Q-crossed and not ODD-bad. This is how Lemma F2 was found.
* The original `local_xp.py odd tightm1 tight0` and `even tightm1 tight0` were rerun: both are
  UNSAT.
