# XP local lemmas P-only and Q-only: human proof

**Status.** This is a complete human proof. It uses only closure, submodularity, exchange and the
multiple symmetric exchange theorem (Greene; Woodall; Greene–Magnanti). Every intermediate claim
was also confirmed by SAT (see the Appendix), but no step of the proof depends on SAT.

**Shape of the argument.**
1. For a valid split, the P-only conclusion fails exactly when the split is *crossed* (Proposition 1).
2. A valid split exists by multiple symmetric exchange.
3. If that split ({u,v},{w,z}) is crossed, one of the two "cover" splits ({u,w},{v,z}) and
   ({u,z},{v,w}) is valid and uncrossed (Theorem 3).

Step 3 has a short proof. Five small incidence lemmas turn "cover split bad" into one of three
simple incidences for each cover split, and each of the 3 × 3 combinations contradicts one of the
lemmas in one line.

---

## 0. Conventions and the standard facts used

M is a matroid of rank 4 with rank function r and closure cl. We write X + e for X ∪ {e}, and
cl(e₁, …, e_k) for cl({e₁, …, e_k}). A 4-element set is a basis if and only if it is independent.
A *flat* is a closed set, and a *plane* is a flat of rank 3.

* **(M1)** Closure is extensive, monotone and idempotent. An intersection of flats is a flat.
* **(M2)** If I is independent and e ∉ I, then I + e is independent if and only if e ∉ cl(I).
* **(M3)** If F is a flat and X ⊆ F, then cl(X) ⊆ F. If moreover r(X) = r(F), then cl(X) = F.
  (Every e ∈ F has r(X + e) ≤ r(F) = r(X).)
* **(M4)** Exchange: if e ∈ cl(X + f) and e ∉ cl(X), then f ∈ cl(X + e).
* **(M5)** Submodularity: r(F ∩ G) + r(F ∪ G) ≤ r(F) + r(G).
* **(M6)** *Two flats meet as expected.* Let F and G be flats of rank k with r(F ∪ G) ≥ k + 1, and
  let X ⊆ F ∩ G be independent with |X| = k − 1. Then F ∩ G = cl(X).
  *Proof.* By (M1), F ∩ G is a flat containing X, so r(F ∩ G) ≥ k − 1. By (M5),
  r(F ∩ G) ≤ 2k − (k + 1) = k − 1. So r(X) = r(F ∩ G), and (M3) gives F ∩ G = cl(X). ∎
* **(M7)** Multiple symmetric exchange (Greene 1973; Woodall 1974; the two-block case of
  Greene–Magnanti 1975): if B and B′ are bases and X ⊆ B, then there is Y ⊆ B′ such that
  (B ∖ X) ∪ Y and (B′ ∖ Y) ∪ X are both bases.

*Parallelism in a contraction.* Let A be independent with |A| = 2, and let e, f ∉ cl(A). Then
"e ‖ f in M/A" means r(A + e + f) = 3. By (M2) and (M3) this is equivalent to f ∈ cl(A + e),
and also to cl(A + e) = cl(A + f).

---

## 1. The statement

There are twelve distinct elements: S = {s₀, s₁, s₂, s₃}, A₋₁ = (x, x̄), A₀ = (a, ā),
A₁ = (b, b̄) and A₂ = (y, ȳ). The P-only lemma uses only these hypotheses:

* **(h1)** S is a basis.
* **(h2)** A₀ ∪ A₁ is a basis.
* **(h3)** {x̄, a, ā, b} is a basis.
* **(t1)** {x, a, ā, b̄} is a basis.
* **(t2)** {x̄, a, ā, b̄} is not a basis.
* **(t3)** {x, a, ā, b} is not a basis.

(t1)–(t3) are the tightness of R₋₁. The remaining hypotheses of `local_xp.py` are not needed:
that A₋₁ ∪ A₀, A₁ ∪ A₂ and {ā, b, b̄, y} are bases. In fact A₋₁ ∪ A₀ being a basis follows from
Step 2 below.

An *ordered split* (P, Q) of S has |P| = |Q| = 2 and P ∪ Q = S. It is **valid** if A₀ ∪ P and
Q ∪ A₁ are bases.

**P-only lemma.** Some valid split (P, Q), orientation P = (p, p̄) and flip ε ∈ {0, 1} make both
Wa = {ℓ_ε} ∪ A₀ ∪ {p} and Wc = {p̄} ∪ Q ∪ {f_ε} bases. Here ℓ₀ = x̄, ℓ₁ = x, f₀ = b and f₁ = b̄.

**Notation.** L := cl(A₀), H := cl(A₀ + b) and H̄ := cl(A₀ + b̄).

### Step 1 (the two planes through L)

By (h2), A₀ + b and A₀ + b̄ are independent, so H and H̄ are planes. Because A₀ ∪ A₁ is
independent, (M2) gives

  **(1a)** b̄ ∉ H and b ∉ H̄.

Apply (M6) with k = 3 and X = A₀; this is allowed because r(H ∪ H̄) ≥ r(A₀ ∪ A₁) = 4. It gives

  **(1b)** H ∩ H̄ = L.

### Step 2 (the windows in terms of H, H̄)

**(2a)** cl(A₀ + x) = H and cl(A₀ + x̄) = H̄.

*Proof.* A₀ + x is independent by (t1), and b ∈ cl(A₀ + x) by (t3) and (M2). So A₀ + b is an
independent 3-set inside the plane cl(A₀ + x), and (M3) gives cl(A₀ + b) = cl(A₀ + x). The same
argument with (h3) and (t2) gives cl(A₀ + x̄) = cl(A₀ + b̄). ∎

Let (P, Q) be a split and (p, p̄) an orientation of P. The set Q + p̄ ⊆ S is independent, and
the twelve elements are distinct. So (M2) and (2a) give:

| ε | Wa is a basis ⟺ | Wc is a basis ⟺ |
|---|---|---|
| 0 | p ∉ H̄ | b ∉ cl(Q + p̄) |
| 1 | p ∉ H | b̄ ∉ cl(Q + p̄) |

Call (P, Q) **successful** if some orientation and some ε satisfy both conditions in the row for ε.

### Step 3 (crossed splits)

**Definition.** A valid split (P, Q) is **crossed** if P can be labelled P = {p, p′} so that

  p ∈ H, p′ ∈ H̄, b̄ ∈ cl(Q + p) and b ∈ cl(Q + p′).

*This agrees with the ‖-definition in the task and in `crossed.py`.* Let (P, Q) be valid.
* p ∉ L, so p ∈ H ⟺ p ‖ b in M/A₀, and p′ ∈ H̄ ⟺ p′ ‖ b̄ in M/A₀.
* Q + p, Q + b and Q + b̄ are independent, so b̄ ∈ cl(Q + p) ⟺ p ‖ b̄ in M/Q, and
  b ∈ cl(Q + p′) ⟺ p′ ‖ b in M/Q.

**Proposition 1.** A valid split is successful if and only if it is not crossed.

*Proof.* Let (P, Q) be valid, with P = {u, v}. Three exclusions hold:

* **(E1)** Neither u nor v lies in L = H ∩ H̄, because A₀ + u + v is independent. So neither lies in both H and H̄.
* **(E2)** For t ∈ P, b and b̄ are not both in cl(Q + t). Otherwise Q ∪ A₁ ⊆ cl(Q + t), which has rank 3.
* **(E3)** u and v are not both in H, and not both in H̄. Otherwise A₀ + u + v lies in a plane.

(⟸) Suppose (P, Q) is not successful. Each of the four (orientation, ε) choices fails:

1. (u, v), ε = 0: u ∈ H̄ or b ∈ cl(Q + v).
2. (u, v), ε = 1: u ∈ H or b̄ ∈ cl(Q + v).
3. (v, u), ε = 0: v ∈ H̄ or b ∈ cl(Q + u).
4. (v, u), ε = 1: v ∈ H or b̄ ∈ cl(Q + u).

Expand 1 ∧ 2. The option u ∈ H̄ ∧ u ∈ H is excluded by (E1), and b, b̄ ∈ cl(Q + v) by (E2).
What remains is

* **(α)** u ∈ H̄ and b̄ ∈ cl(Q + v), or
* **(β)** u ∈ H and b ∈ cl(Q + v).

In the same way 3 ∧ 4 gives

* **(γ)** v ∈ H̄ and b̄ ∈ cl(Q + u), or
* **(δ)** v ∈ H and b ∈ cl(Q + u).

(α ∧ γ) and (β ∧ δ) contradict (E3). (α ∧ δ) is crossed with (p, p′) = (v, u), and (β ∧ γ) is
crossed with (p, p′) = (u, v).

(⟹) Suppose (P, Q) is crossed via (p, p′). Then every choice fails:

* orientation (p, p′), ε = 0 fails because b ∈ cl(Q + p′);
* orientation (p, p′), ε = 1 fails because p ∈ H;
* orientation (p′, p), ε = 0 fails because p′ ∈ H̄;
* orientation (p′, p), ε = 1 fails because b̄ ∈ cl(Q + p). ∎

So the P-only lemma is equivalent to the **core claim**: some valid split is not crossed. Only the
direction (⟸) is used below. The core claim involves only the 8 elements a, ā, b, b̄ and S, and
the hypotheses (h1) and (h2).

---

## 2. The core claim

**Theorem 2 (core).** Let M have rank 4, and let A₀ = {a, ā}, A₁ = {b, b̄} and S be pairwise
disjoint, with A₀ ∪ A₁ and S bases. Then some valid split of S is not crossed.

The notation L, H, H̄ and facts (1a), (1b) from Step 1 use only (h2), so they are available.

### Step 4 (a valid split exists)

Apply (M7) with B = A₀ ∪ A₁, X = A₁ and B′ = S. It gives Y ⊆ S with A₀ ∪ Y and (S ∖ Y) ∪ A₁ bases.
Since S ∩ A₀ = ∅, |Y| = 2. So (Y, S ∖ Y) is a valid split.

### Step 5 (setup: a crossed valid split)

If the split from Step 4 is not crossed, we are done. Otherwise label it (P, Q) = ({u, v}, {w, z}),
with (p, p′) = (u, v) in the definition. We then have:

* **(X1)** u ∈ H
* **(X2)** v ∈ H̄
* **(X3)** b̄ ∈ cl(u, w, z)
* **(X4)** b ∈ cl(v, w, z)

together with the independence facts

* **(B1)** {u, v, w, z} is independent;
* **(B2)** A₀ + u + v is independent;
* **(B3)** {w, z, b, b̄} is independent.

Consequences:

* **(F1)** u ∉ H̄ and v ∉ H. By (B2), u, v ∉ L = H ∩ H̄, and then (X1), (X2) and (1b) apply.
* **(F2)** cl(A₀ + u) = H. By (B2), A₀ + u is an independent 3-set in the plane H, so (M3) applies.
* **(F3)** b ∉ cl(t) for t ∈ {w, z}, because {t, b} ⊆ Q ∪ A₁ is independent.

The two **cover splits** are C_w := ({u, w}, {v, z}) and C_z := ({u, z}, {v, w}). Below,
{t, t′} = {w, z} in either order.

### Step 6 (five small lemmas)

**Lemma A.** w and z are not both in H, and not both in H̄.

*Proof.* Suppose w, z ∈ H. Then {u, w, z} ⊆ H by (X1). This set is independent of rank 3 by (B1),
so cl(u, w, z) = H by (M3). Now (X3) gives b̄ ∈ H, contradicting (1a).

Suppose w, z ∈ H̄. Then {v, w, z} ⊆ H̄ by (X2), so cl(v, w, z) = H̄, and (X4) gives b ∈ H̄,
again contradicting (1a). ∎

**Lemma B.** b does not lie in both cl(v, w) and cl(v, z).

*Proof.* cl(v, w) and cl(v, z) are rank-2 flats, and their union has rank r(v, w, z) = 3 by (B1).
(M6) with k = 2 and X = {v} gives cl(v, w) ∩ cl(v, z) = cl(v). So b ∈ cl(v) ⊆ H̄, using (X2) and
(M3). This contradicts (1a). ∎

**Lemma C (A₁-side validity).** If b ∉ cl(v, t), then {v, t} ∪ A₁ is a basis.

*Proof.* The set {v, t} is independent by (B1), and b ∉ cl(v, t), so {v, t, b} is independent (M2).
It lies in the plane G := cl(v, w, z) by (X4), so cl(v, t, b) = G by (M3).

Suppose {v, t, b, b̄} were dependent. Then b̄ ∈ cl(v, t, b) = G by (M2). So {w, z, b, b̄} ⊆ G has
rank at most 3, contradicting (B3). ∎

**Lemma D (A₀-side validity).** If t ∉ H, then A₀ ∪ {u, t} is a basis.

*Proof.* A₀ + u is independent and cl(A₀ + u) = H by (F2). Apply (M2). ∎

**Lemma E (incidences).**

* **(a)** If b ∈ cl(v, t), then t ∉ H and t ∉ H̄.
* **(b)** If b̄ ∈ cl(u, t), then t ∉ H.

*Proof.* (a) First, t ∉ H. We have b ∉ cl(t) by (F3), so (M4) gives v ∈ cl(t, b). If t ∈ H, then
{t, b} ⊆ H, so v ∈ cl(t, b) ⊆ H, contradicting (F1).
Second, t ∉ H̄. If t ∈ H̄, then {v, t} ⊆ H̄ by (X2), so b ∈ cl(v, t) ⊆ H̄, contradicting (1a).

(b) If t ∈ H, then {u, t} ⊆ H by (X1), so b̄ ∈ cl(u, t) ⊆ H, contradicting (1a). ∎

**Lemma F (when a cover split is crossed).** If C_t = ({u, t}, {v, t′}) is valid and crossed,
then t ∈ H̄ and b̄ ∈ cl(u, t′).

*Proof.* Take the labelling (p, p′) of {u, t} from the definition of crossed.

If p = t and p′ = u, then u ∈ H̄, contradicting (F1). So p = u and p′ = t. This gives t ∈ H̄ and
b̄ ∈ cl({v, t′} + u) = cl(u, v, t′).

Also b̄ ∈ cl(u, t, t′) by (X3). The planes cl(u, v, t′) and cl(u, t, t′) have union of rank 4
by (B1), and both contain the independent set {u, t′}. (M6) with k = 3 gives
cl(u, v, t′) ∩ cl(u, t, t′) = cl(u, t′). Hence b̄ ∈ cl(u, t′). ∎

### Step 7 (the cover theorem)

**Theorem 3.** In the setting of Step 5, C_w or C_z is valid and not crossed.

*Proof.* Suppose both are bad, meaning invalid or crossed.

If C_w is invalid, then A₀ ∪ {u, w} or {v, z} ∪ A₁ is not a basis. By Lemmas D and C, w ∈ H or
b ∈ cl(v, z). If C_w is crossed, then by Lemma F (t = w, t′ = z), w ∈ H̄ and b̄ ∈ cl(u, z).
So C_w bad gives one of:

* **(i)** w ∈ H;
* **(ii)** b ∈ cl(v, z);
* **(iii)** w ∈ H̄ and b̄ ∈ cl(u, z).

The same argument with w and z exchanged shows that C_z bad gives one of:

* **(i′)** z ∈ H;
* **(ii′)** b ∈ cl(v, w);
* **(iii′)** z ∈ H̄ and b̄ ∈ cl(u, w).

Each of the nine combinations is contradictory:

| C_w bad \ C_z bad | (i′) z ∈ H | (ii′) b ∈ cl(v,w) | (iii′) z ∈ H̄, b̄ ∈ cl(u,w) |
|---|---|---|---|
| **(i)** w ∈ H | Lemma A (w, z ∈ H) | Lemma E(a), t = w: w ∉ H | Lemma E(b), t = w: w ∉ H |
| **(ii)** b ∈ cl(v,z) | Lemma E(a), t = z: z ∉ H | Lemma B | Lemma E(a), t = z: z ∉ H̄ |
| **(iii)** w ∈ H̄, b̄ ∈ cl(u,z) | Lemma E(b), t = z: z ∉ H | Lemma E(a), t = w: w ∉ H̄ | Lemma A (w, z ∈ H̄) |

∎

### Step 8 (proof of Theorem 2)

By Step 4 some valid split exists. If it is not crossed, we are done. If it is crossed, label it
as in Step 5; Theorem 3 gives a valid split that is not crossed. ∎

### Step 9 (proof of the P-only lemma)

Theorem 2 needs only (h1), (h2) and the distinctness of the elements, so it gives a valid split
(P, Q) that is not crossed. By Proposition 1 (⟸), (P, Q) is successful. That is, some
orientation (p, p̄) and some ε make Wa and Wc bases. ∎

**Length.** The core (Steps 4–8) takes about one page: six lemmas of two to four lines each and a
3 × 3 table. The reduction (Steps 1–3) takes about half a page. The only case analysis is the
table in Step 7 and the four-clause expansion in Proposition 1.

---

## 3. The mirror lemma Q-only (via reversal)

### Statement, as encoded by `python local_xp.py Qonly tight0`

The hypotheses are:

* S, A₀ ∪ A₁ and {ā, b, b̄, y} are bases (A₋₁ ∪ A₀, A₁ ∪ A₂ and {x̄, a, ā, b} are also given, but not used);
* **tightness of R₀**: {a, b, b̄, ȳ} is a basis, and {ā, b, b̄, ȳ} and {a, b, b̄, y} are not bases.

In M/A₁ this says a ‖ y and ā ‖ ȳ.

**Claim (Q-only).** Some valid split (P, Q), orientation Q = (q, q̄) and flip e ∈ {0, 1}
make both of these bases:

* Wb = {last A′₀} ∪ P ∪ {first Q} = {m_e} ∪ P ∪ {q};
* Wd = {last Q} ∪ A₁ ∪ {first A′₂} = {q̄} ∪ A₁ ∪ {g_e}.

Here A′₀ = A₀ and A′₂ = A₂ when e = 0, and both are flipped when e = 1. So m₀ = ā, m₁ = a, g₀ = y
and g₁ = ȳ.

### The reversal

Reverse the sequence …, A₋₁, A₀, [P, Q], A₁, A₂, … and reverse each pair inside it. The first
element of a reversed pair is the last element of the original pair. So a window
{last X} ∪ Y ∪ {first Z} becomes {last Z^rev} ∪ Y ∪ {first X^rev}, which is the same set.

Apply the P-only lemma, in the same matroid M, to the following relabelled instance (starred):

| starred (P-only role) | original element | reason |
|---|---|---|
| A*₋₁ = (x*, x̄*) | (ȳ, y) | A₂ reversed |
| A*₀ = (a*, ā*) | (b̄, b) | A₁ reversed |
| A*₁ = (b*, b̄*) | (ā, a) | A₀ reversed |
| A*₂ = (y*, ȳ*) | (x̄, x) | A₋₁ reversed (not used) |
| S* | S | |
| split (P*, Q*) | (Q, P) | P and Q swap sides |
| orientation P* = (p*, p̄*) | Q = (q, q̄) with q = p̄*, q̄ = p* | Q reversed |
| flip ε | e | flips A*₋₁, A*₁ = flips A₂, A₀ together |

**The hypotheses translate exactly.**

| P-only hypothesis (starred) | original set | status in Q-only |
|---|---|---|
| (h1) S* basis | S | given |
| (h2) A*₀ ∪ A*₁ basis | A₁ ∪ A₀ | given |
| (h3) {x̄*, a*, ā*, b*} basis | {y, b̄, b, ā} | given (σ-window {ā, b, b̄, y}) |
| (t1) {x*, a*, ā*, b̄*} basis | {ȳ, b̄, b, a} | tight0 |
| (t2) {x̄*, a*, ā*, b̄*} not a basis | {y, b̄, b, a} | tight0 |
| (t3) {x*, a*, ā*, b*} not a basis | {ȳ, b̄, b, ā} | tight0 |

**Validity translates.** (P*, Q*) = (Q, P) is valid for the starred instance when A*₀ ∪ P* =
A₁ ∪ Q and Q* ∪ A*₁ = P ∪ A₀ are bases. That is exactly the validity of (P, Q) in the original.

**The windows translate.** Recall ℓ*₀ = x̄* = y, ℓ*₁ = x* = ȳ, f*₀ = b* = ā and f*₁ = b̄* = a. Then:

* Wa* = {ℓ*_ε} ∪ A*₀ ∪ {p*} = {g_e} ∪ A₁ ∪ {q̄} = **Wd** (g₀ = y, g₁ = ȳ);
* Wc* = {p̄*} ∪ Q* ∪ {f*_ε} = {q} ∪ P ∪ {m_e} = **Wb** (m₀ = ā, m₁ = a).

So the P-only lemma for the starred instance gives a valid (P*, Q*), an orientation (p*, p̄*) and
an ε with Wa* and Wc* bases. The translation above gives a valid split (P, Q) = (Q*, P*), the
orientation Q = (p̄*, p*) and e = ε, with Wb and Wd bases. This is the Q-only lemma. ∎

**Unfolded mirror statement.** For the reader who wants it without relabelling: a valid split
(P, Q) fails Q-only exactly when it is *mirror-crossed*. That means Q = {q₁, q₂} with

* q₁ ∈ cl(A₁ + ā) and q₂ ∈ cl(A₁ + a), i.e. q₁ ‖ ā and q₂ ‖ a in M/A₁;
* a ∈ cl(P + q₁) and ā ∈ cl(P + q₂), i.e. q₁ ‖ a and q₂ ‖ ā in M/P.

The mirror of Theorem 3 reads as follows. Let (P, Q) = ({p₁, p₂}, {q₁, q₂}) be valid and
mirror-crossed as above. Then one of the splits ({q₂, p₂}, {q₁, p₁}) and ({q₂, p₁}, {q₁, p₂}) is
valid and not mirror-crossed.

To see this, note that in the starred instance u* = q₁, v* = q₂ and {w*, z*} = Q* = P. The cover
split C*_t = ({q₁, t}, {q₂, t′}), with {t, t′} = P, translates back to (P, Q) = ({q₂, t′}, {q₁, t}).
We do not need to state this separately; it is Theorem 3 transported by the table above. It was
also confirmed by SAT (`mirror_cover.py`). Note that the tightness hypothesis
changes from (t1)–(t3) on A₋₁ to tight0 on A₂. With the wrong tightness both lemmas fail
(Appendix, controls).

---

## 4. Remarks and checks of the partial progress in the task

1. **The reduction to the core** (Proposition 1) is exact in both directions. It uses only
   (h1)–(h3) and (t1)–(t3).
2. **Partial-progress items.** All of them are correct.
   * "b ∈ cl(A₀ + u) ∩ cl(Q + v) and b̄ ∈ cl(A₀ + v) ∩ cl(Q + u)": this is (F2), (X1)–(X4).
   * "Q ⊄ H, Q ⊄ H̄": this is Lemma A. Q ⊄ L follows, since L ⊆ H.
   * "v ∉ cl(A₁)": if v ∈ cl(A₁), then {v, w} ∪ A₁ and {v, z} ∪ A₁ are both dependent. Lemma C
     then gives b ∈ cl(v, w) ∩ cl(v, z), contradicting Lemma B. The setup of Step 5 is symmetric
     under u ↔ v, b ↔ b̄, H ↔ H̄, (X1) ↔ (X2), (X3) ↔ (X4). Applying Lemmas B and C under that
     swap gives u ∉ cl(A₁).
   * The two "one of the covers is valid on each side" statements are correct. They are not enough
     on their own; the missing ingredients were Lemma F (a crossed cover split forces b̄ onto the
     line cl(u, t′)) and the incidence Lemma E.
3. **The reversed split ({w, z}, {u, v}) is never crossed.** Suppose it were, via (p, p′), with
   {p, p′} = {w, z}. Then b ∈ cl(u, v, p′) ∩ cl(v, w, z). By (M6) with k = 3 and X = {v, p′},
   this intersection is cl(v, p′). Lemma E(a) then gives p′ ∉ H̄, contradicting p′ ∈ H̄.
4. **What each lemma uses.**
   * Lemma A: (X3), (X4).
   * Lemma B: (X2).
   * Lemma C: (X4) and (B3).
   * Lemma E: (F1), (F3), (X1), (X2).
   * Lemma F: (F1), (X3).

   Only one of the two "Lemma B" statements is needed (the one for b through v). The analogous
   statement for b̄ through u also holds but is not used.

---

## Appendix: SAT confirmations (not used by the proof)

The scripts are in `experiments/rank4_heavy_flat_splice/handproof_pq/` (and `local_xp.py`, `crossed.py` one level up). Each uses the full rank-function encoding of `crossed.py` /
`local_xp.py` (all rank axioms, CaDiCaL 1.9.5).

* **`check_lemmas.py`** (8 elements, with the Step 5 hypotheses). Each of these is UNSAT when
  negated:
  * (F1), Lemma D;
  * Lemma A (both parts), Lemma B;
  * Lemma C (t = w, z);
  * Lemma E (all six instances);
  * Lemma F (both conclusions, for C_w and C_z);
  * Theorem 3.
* **`controls.py`**:
  * the Step 5 hypotheses are satisfiable;
  * each single cover split can be bad, so both are needed;
  * each of (i), (ii) and (iii) can occur.
* **`reduction.py`** (10 elements, *only* the hypotheses listed in §1 and §3):
  * P-only holds (UNSAT);
  * for a fixed valid split, "fails ∧ not crossed" and "crossed ∧ succeeds" are both UNSAT
    (Proposition 1, both directions), and "crossed" is possible;
  * the same for Q-only with mirror-crossing.
* **`mirror_cover.py`**: the transported cover theorem (§3) is UNSAT when negated.
* **`local_xp.py`** (12 elements, original):
  * `Ponly tightm1` and `Qonly tight0` are UNSAT (they hold);
  * controls `Ponly`, `Qonly`, `Ponly tight0` and `Qonly tightm1` are SAT (they fail). So the
    right tightness hypothesis is needed.
* **`crossed.py claim` / `cover`**: UNSAT. The minimal covers are {C_w, C_z} and its mirror,
  which matches Theorem 3.
