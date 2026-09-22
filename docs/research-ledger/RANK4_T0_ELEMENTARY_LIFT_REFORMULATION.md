# Rank-4 t=0 elementary-lift / rank-three quotient reformulation

Date: 2026-09-21.

Branch: `rank4-t0-elementary-lift-reformulation`.

Status: conceptual research checkpoint.  The elementary-lift statements below
use the classical Crapo--Brylawski description of elementary lifts by a linear
class of circuits.  The rank-4 KUM consequences are not Lean-certified unless
explicitly stated otherwise.

## 1. The fixed-e pair (D,N)

Fix the omitted nonloop `e` in the t=0 branch and set

`D = M \ e`,    `N = M / e`.

Both matroids have the same ground set `E(M)-{e}`.

- `D` has rank 4 and `4k+1` elements.
- `N` has rank 3.
- `D` is an elementary lift of `N`: the witness is the original matroid
  `M`, since `M\e=D` and `M/e=N`.

By the Crapo--Brylawski theorem, this elementary lift is determined by a
linear class `B` of circuits of `N`.  Call circuits in `B` **balanced**
and circuits outside `B` **unbalanced**.

For every `X` in the common ground,

`r_D(X)=r_N(X)`

iff every circuit of `N|X` is balanced, while otherwise

`r_D(X)=r_N(X)+1`.

This is an exact rank formula, not an analogy.

## 2. Sliding windows and unique quotient circuits

Let `sigma=(x_i)` be a deletion CBO of `D`, and let

`B_i={x_i,x_{i+1},x_{i+2},x_{i+3}}`.

Each `B_i` is a rank-4 basis of `D`.  Since `N` has rank 3,
`r_N(B_i)=3`.  Thus `N|B_i` has nullity one and a unique circuit
`Q_i subset B_i`.

Because `B_i` gains one rank in the lift, `Q_i` is unbalanced.

Moreover `Q_i` is exactly the old fundamental circuit of `e` with `e`
deleted:

`Q_i = C_M(e,B_i)-{e}`.

The blocker word has the exact quotient-circuit description

`b_i=1  <=>  Q_{i-1}=Q_i`.

Thus insertion failure is persistence of the unique unbalanced quotient
circuit while the rank-4 basis window slides.

## 3. Blockers and Type-I repair gates in the same language

A consecutive triple `T` is a blocker iff

`e in cl_M(T)`

iff

`r_N(T)=2`.

Since `T` is independent in `D`, this means `T` contains an unbalanced
circuit of `N`.

Now let `C` be a nonblocker triple.  Then `C` is a basis of `N`.
For an incoming element `y`, the four-set `C+y` has a unique fundamental
circuit

`R=C_N(y,C)`.

The candidate four-set is a basis of `D` iff `R` is unbalanced.
Therefore a failed Type-I repair gate is exactly

`R in B`,

i.e. a **balanced fundamental circuit**.

So the repair dynamics is an alternating balanced/unbalanced circuit system
inside one rank-three matroid:

- every current rank-4 window carries one unique unbalanced circuit;
- every failed single-exchange repair exposes a balanced fundamental circuit.

## 4. Minimum modular-cut rank = minimum unbalanced-circuit size

Let

`q = min{|Q| : Q circuit of N, Q notin B}`.

This is the minimum rank of a flat of `D` spanning `e`.
It is not ordinary girth of `N`: balanced loops/parallel pairs may exist.

The blocker-run hierarchy becomes

`maximum blocker-run length = 4-q`.

Hence:

- `q=3`: blockers are isolated;
- `q=2`: blocker runs have length at most 2;
- `q=1`: blocker runs have length at most 3.

The long growing-distance binary witnesses all lie in `q=1`.
An explicit GF(3) n=14 distance-two witness exists in `q=2`.
No tested `q=3` state has required more than one four-block repair.

## 5. q=3 evidence and canonical local repair

In the `q=3` case, two consecutive blockers are impossible: their overlapping
triples would force a rank-2 red flat.

Therefore every bad blocker word consists of isolated 1s with zero-runs of
length 1,2,3.  Since the cycle length is `4k+1`, some zero-run has length
exactly 2, giving the canonical pattern

`1 0 0 1`.

The middle adjacent transposition destroys both endpoint blockers under
`q=3`.  If it preserves the deletion CBO, it immediately creates four
consecutive nonblockers.  Its only possible failures are two Type-I boundaries,
and both retained triples are nonblockers.

Empirical checks:

- exact listed GF(3)/GF(5) n=10 q=3 states: 982 bad CBOs, all one-step;
- exact SQS(10): 5,280 bad states, all one-step;
- random simple GF(3) n=14 stress: 183 bad q=3 states, all one-step.

Five transpositions suffice for the n=10/SQS checks; arbitrary four-block
moves remain the safer theorem statement.

Candidate local theorem:

`q=3 => every bad deletion CBO has a one-step four-block repair`.

## 6. q=2 is genuinely multi-step

A GF(3) n=14 witness satisfies the full t=0/two-deletion robustness package
and has:

- ambient flat profile `(1,4,8)`;
- minimum unbalanced-circuit size `q=2`;
- no saturated 9-point rank-3 flat through `e`;
- blocker word `0101100110101`;
- no favorable one-step four-block move;
- exact fixed-e repair distance 2.

Thus the q=3 one-step behavior does not extend to q=2.

Principal-q=2 stress (one nontrivial unbalanced parallel class in N) is much
cleaner: 1,000 sampled bad GF(3) n=14 CBOs all had a favorable one-step
arbitrary four-block move.  This is evidence only.

## 7. Density becomes biased rank-three geometry

For `X` in the common ground:

- if `X` is balanced, `r_D(X)=r_N(X)`;
- if `X` is unbalanced, `r_D(X)=r_N(X)+1`.

The deletion density of `D` therefore gives these useful rank-three caps:

- balanced rank-1 set: size at most `k`;
- balanced rank-2 set: size at most `2k`;
- balanced rank-3 hyperplane: size at most `3k`;
- unbalanced rank-2 flat: size at most `3k-1` in the no-dangerous branch.

The desired saturated endpoint is exactly an **unbalanced rank-2 flat of N
with 3k-1 deletion elements**.  Adding `e` gives the 3k-point rank-three
flat in M.

A failed Type-I gate with retained N-basis `C` aggregates automatically into
the balanced D-hyperplane

`K_C = cl_D(C)`.

Indeed an outside element `y` lies in `K_C` exactly when the fundamental
N-circuit `C_N(y,C)` is balanced.

So the two large objects seen in hard repair paths are naturally:

- near-tight unbalanced lines of N;
- near-tight balanced planes of N.

## 8. Density-slack identity for unbalanced lines

If `F` is an unbalanced rank-2 flat of N, then it has D-rank 3.
For the deletion ground size `4k+1`, define

`delta(F)=3(4k+1)-4|F|`.

This is simultaneously:

1. the rank-3 density slack of `F` in `D`;
2. the four-window incidence excess of the complementary fundamental
   exchange star.

The no-dangerous cap is `delta(F)>=7`, and the desired saturated endpoint is

`delta(F)=7`.

If `|F|=3k-1-d`, then `delta(F)=7+4d`.

Thus every missing element from saturation costs exactly four units of slack.

## 9. Balanced 3k-hyperplane endpoint

Suppose `K` is a balanced D-hyperplane of size `3k`.

Then `D|K=N|K` has rank 3.  Every rank-1/rank-2 subset inherits the sharp
bounds `k,2k` from D-density, so `D|K` is uniformly dense at ratio
`3k/3=k`.

Therefore the solved rank-three KUM theorem gives a cyclic basis ordering of
`K`.

This does not by itself solve the full rank-four instance.  However `K` has
exactly `k+2` outside elements in the full matroid M.  The cardinalities are
therefore identical to the existing six-defect saturated-flat gluing setup:

- 3k elements in the rank-three core;
- k+2 outside elements;
- skeleton `(HHHR)^(k-2) HHHR HR HH RR`;
- every ordinary four-window is 3H+1R;
- exactly six exceptional windows are 2H+2R.

Hence a balanced 3k hyperplane reduces the full problem to the **same
constant-size six-window gluing interface** already supported by exact n=10
and historical n=18 saturated-flat experiments.

A general six-defect gluing theorem is still missing.

## 10. Interpretation

The t=0 problem can be recast as:

> Given a rank-4 elementary lift D of a rank-3 matroid N on 4k+1 elements,
> together with a linear class B of balanced circuits, start from a cyclic
> rank-4 basis ordering of D.  Each four-window has one unique unbalanced
> N-circuit.  Reorder locally until four consecutive triple overlaps are
> N-independent.

The long repair chains are not generating new local matroid mechanisms.
They reflect increasing degeneracy of the elementary quotient:

- q=3: smallest unbalanced circuits are triangles; observed one-step behavior;
- q=2: unbalanced parallel pairs; multi-step appears;
- q=1: unbalanced loops in N, equivalently e parallel in M; growing distances.

This suggests that the global component theorem should be attacked as
**rank-three biased geometry** rather than as an arbitrary rank-four
reconfiguration graph.

## Next task

Prove or falsify a rank-three biased-geometry dichotomy strong enough to close
a trap:

> A closed terminal-free four-block component forces either
> (a) an unbalanced rank-2 flat of size 3k-1, or
> (b) a balanced rank-3 hyperplane of size 3k.

Then:
- (a) is the saturated red endpoint;
- (b) reduces to the constant six-defect gluing problem above.

Before Lean formalization, test this dichotomy on the exact binary n=10 class,
the historical n=18 witness, the growing n=14..30 family, GF(3)/GF(5), and
sparse-paving examples.
