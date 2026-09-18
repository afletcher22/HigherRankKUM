# Density slack and single-element deletion

Checked informal arguments, 2026-09-18. These statements are not yet Lean
formalized and no novelty claim is made. They do not prove insertion or KUM.

Throughout, M is a finite uniformly dense matroid, n=|E|>r=r(M)>0.
Strict means r|A|<n r(A) for every nonempty proper ground-set subset.
Write m_j=max{|A|:r(A)=j}, delta_j=nj/r-m_j, s_j=nj-rm_j.
Maxima may be taken over flats. Only 1<=j<r is used.

## 1. Exact universal deletion criterion (arbitrary rank)

Every single-element deletion is uniformly dense if and only if s_j>=j for
every 1<=j<r (equivalently delta_j>=j/r).

Proof. Uniform density excludes loops. It also excludes coloops when n>r:
a coloop would give r(n-1)<=n(r-1), hence n<=r. Thus every deletion has rank r.
For sufficiency, each rank-j subset of a deletion has cardinality at most m_j,
and r m_j<= (n-1)j. Rank-zero subsets are empty; rank-r subsets have size at
most n-1. For necessity, take a maximizing rank-j set and delete an element
outside it; the deletion density inequality gives the claimed bound. QED.

## 2. Strict integral density (arbitrary rank)

If n=kr, k>=2, and M is strict, every deletion is uniformly dense.

Proof. For 1<=j<r, strictness and integer cardinalities give m_j<=kj-1.
Consequently s_j>=r>j, and the preceding criterion applies. QED.

Since gcd(kr-1,r)=1, the coprime theorem supplies a cyclic basis order of
each deletion mathematically. It does NOT supply an order permitting insertion
of the missing element. The coprime theorem is an external mathematical input,
not an internally formalized dependency here.

## 3. Strict rank four, n=4k+2

Let k>=1. Call a rank-three flat dangerous when it has 3k+1 elements.
Then M\e fails uniform density exactly when some dangerous flat avoids e.

Proof. Strictness gives m_1<=k, m_2<=2k, m_3<=3k+1. After deletion, the
rank-1,2,3 cardinality bounds are respectively k,2k,3k. Hence failure is
exactly a rank-three set A of size 3k+1 avoiding e. Such A is already a flat:
closure preserves rank, and any extra element would violate m_3<=3k+1. QED.

### Pairwise disjoint dangerous complements

Distinct hyperplanes H,K have r(H intersection K)<=2: their intersection is a
flat properly contained in each rank-three flat. Thus |H intersection K|<=2k.
If both are dangerous, inclusion-exclusion gives

    |H union K| >= 2(3k+1)-2k = 4k+2 = n.

Equality follows. Hence H union K=E, |H intersection K|=2k, and the
complements E\H and E\K are disjoint. Each complement has size k+1.
There are consequently at most floor((4k+2)/(k+1))=3 dangerous hyperplanes.

### Quantitative good-deletion theorem

If t is the number of dangerous hyperplanes, the number of elements whose
deletion preserves uniform density is EXACTLY

    4k+2 - t(k+1),    where 0<=t<=3.

In particular it is at least k-1. For k>=2 there is always a good deletion.
For k=1 this bound is zero, so the argument makes no existence claim.

Combined with Section 2, every strict rank-four matroid of EVEN size n>=8
has a uniformly dense single-element deletion. That deletion has odd size,
so its CBO exists by coprimality. This reduces the remaining strict even
rank-four problem to a precisely quantified insertion question:

    Does SOME good element e and SOME CBO of M\e admit a suitable extension?

Preserving that entire cyclic order by insertion in one gap is an additional
restriction and is not asserted. A repair/reordering theorem could instead be
required. No induction assumption should silently supply a favorable order.

## 4. Connection to the ongoing closure proof

For rank four on 2N elements, delta_2=N-m_2. Every block closure in an
admissible pair cycle has size at most N-delta_2. Thus a lower bound exceeding
this capacity contradicts density. Incidences in different rank-two flats
must NOT be counted as accumulating in one flat without a propagation theorem.
The density profile is invariant under re-pairing and cannot itself be a
strictly increasing repair potential.

## 5. Regression evidence and limitations

experiments/density_slack_deletion_certificate.py exhaustively checks subsets
of two historical binary witnesses, a six-element boundary example, and 160 deterministically seeded binary
examples. It checks the exact universal criterion, strict integral deletion,
the dangerous-hyperplane characterization, pairwise-disjoint complements,
and the k-1 lower bound. Repeated vectors denote labelled parallel elements.
The sample is NOT an exhaustive classification and is NOT a proof in other
fields or nonrepresentable matroids; Sections 1-3 provide the general proofs.

Both historical witnesses have integer slack vector (2,4,2), equivalently
delta=(1/2,1,1/2). The ten-element witness has two dangerous hyperplanes and
four good deletions. The eighteen-element witness has three dangerous
hyperplanes and three good deletions, attaining k-1 for k=4.

The six-element binary representation (13,1,14,2,4,8) is strict but has
three dangerous hyperplanes and NO good deletion. Thus the k>=2 existence
boundary cannot simply be dropped.

The same script audits all deletion CBOs modulo rotation (reversal remains
distinct) and all single insertion gaps for every good element of the
ten-element witness. Its output records any failure of the every-order
strengthening; it does not extrapolate the result to all matroids.

For the ten-element witness, the good labels are 0,4,7,8 (zero-based).
The counts (deletion CBOs, those permitting a single-gap insertion) are:

| Deleted label | Deletion CBOs | Extendable |
|---|---:|---:|
| 0 | 368 | 56 |
| 4 | 368 | 56 |
| 7 | 224 | 88 |
| 8 | 336 | 56 |

Thus even the strengthening "some good element works with EVERY deletion
CBO" is false: EACH good element has a nonextendable order. The weaker
"some good element and some order" survives this experiment. Nonextendable
means only that insertion into any ONE gap, preserving the remaining cyclic
order, fails. It is not a counterexample to more flexible reinsertion or KUM.

Reference: van den Heuvel--Thomasse, Cyclic Orderings and Cyclic Arboricity of
Matroids, https://arxiv.org/abs/0912.2929 (coprime theorem).
