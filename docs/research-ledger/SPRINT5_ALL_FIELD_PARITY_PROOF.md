# Sprint 5 — all-field represented six-block parity proof

Date: 2026-09-16/17.

Status: checked informal linear-algebra proof; not yet formalized in Lean.

## The local theorem

Let a rank-four matroid be represented over an arbitrary field `K`.  Consider
six consecutive two-element blocks

`A,B,C,D,E,F`

of an admissible pair cycle.  Assume the four old endpoint relations

`T(A,B,C), T(B,C,D), T(C,D,E), T(D,E,F)`

are forced bijections.  Repartition `C union D` into two pairs `Q,R`, preserve
the two changed aligned bases, and assume all four new endpoint relations

`T(A,B,Q), T(B,Q,R), T(Q,R,E), T(R,E,F)`

remain forced bijections.

Then the XOR of the four new identity/flip bits is equal to the XOR of the
four old bits.

Equivalently: in every rank-four matroid representable over **any field**, a
forced-preserving adjacent pair repartition preserves the local forced parity.
Hence an obstructed represented pair cycle cannot escape solely by changing
forced parity; a local escape must create slack at an affected relation.

This is a local theorem.  It does not assert existence of a legal/productive
repartition and does not cover nonrepresentable matroids.

## 1. Gauge normalization

The four old relations connect the endpoint-label bits along the two paths

`A -- C -- E` and `B -- D -- F`.

Swapping the labels of a block toggles the incident identity/flip labels.
Because these are paths, choose block labels so that **all four old relations
are identity**.  This changes neither the truth of the parity-conservation
statement nor the set of underlying unordered repartitions.

Similarly, after a repartition the labels inside `Q` and `R` may be chosen for
convenience.  Swapping the labels of `Q` toggles two of the four new relation
bits, and likewise for `R`, so the XOR of the four new bits is label-invariant.

Thus it suffices to prove that, in one convenient labelling, every
forced-preserving repartition has even new parity.

## 2. Coordinate normal form

Since `C union D` is a basis, row operations and independent nonzero column
scalings put

```
C = {c0,c1},   D = {d0,d1}
```

at the coordinate basis of `K^4`.

The identity relation `T(B,C,D)` says that modulo `span(C)`, the two columns of
`B` are parallel to `d0,d1` respectively.  After scaling them,

```
b0 = d0 + a c0 + b c1,
b1 = d1 + c c0 + d c1.
```

Likewise `T(C,D,E)=id` gives

```
e0 = c0 + u d0 + v d1,
e1 = c1 + w d0 + z d1.
```

The two outer identity relations allow

```
a0 = c0 + r b0 + s b1,
a1 = c1 + t b0 + l b1,

f0 = d0 + m e0 + n e1,
f1 = d1 + o e0 + p e1.
```

The outer coefficients `r,s,t,l,m,n,o,p` disappear from every determinant
below.  This is why the six-block parity calculation factorizes so strongly in
the exact finite-field audits.

For a relation matrix, rows are the first endpoint state `x=0,1`, columns are
the last endpoint state `y=0,1`, and an entry is the determinant of the
corresponding four columns.  A forced identity has nonzero diagonal entries
and zero off-diagonal entries; a forced flip has zero diagonal entries and
nonzero off-diagonal entries.

The four old relation matrices reduce to

```
[[-1,0], [0,1]],
```

so they are identity over every characteristic (with `-1=1` in
characteristic two).

## 3. The four cross repartitions

There are four ordered cross repartitions of the middle basis, up to the
chosen labels, plus the wholesale swap.

### Case I

```
Q={c0,d0}, R={c1,d1}.
```

The four new determinant matrices are

```
T(A,B,Q) = [[-1, a], [ 0,-b]],
T(B,Q,R) = [[ 1,-d], [ 0,-b]],
T(Q,R,E) = [[ 1, 0], [-u,-w]],
T(R,E,F) = [[-1, 0], [ z,-w]].
```

If all four are forced, necessarily

```
a=d=u=z=0,   b != 0,   w != 0.
```

All four new relations are identity.  New parity: `0`.

### Case II

```
Q={c0,d1}, R={c1,d0}.
```

The matrices are

```
T(A,B,Q) = [[-1, c], [ 0,-d]],
T(B,Q,R) = [[ 0, d], [-1, b]],
T(Q,R,E) = [[-1, 0], [ v, z]],
T(R,E,F) = [[ 0, 1], [ z,-w]].
```

Forcedness gives

```
c=b=v=w=0,   d != 0,   z != 0.
```

The orientations are

`identity, flip, identity, flip`.

New parity: `0`.

### Case III

```
Q={c1,d0}, R={c0,d1}.
```

The matrices are

```
T(A,B,Q) = [[ 0, a], [ 1,-b]],
T(B,Q,R) = [[-1, c], [ 0, a]],
T(Q,R,E) = [[ 0,-1], [ u, w]],
T(R,E,F) = [[-1, 0], [ v,-u]].
```

Forcedness gives

```
b=c=w=v=0,   a != 0,   u != 0.
```

The orientations are

`flip, identity, flip, identity`.

New parity: `0`.

### Case IV

```
Q={c1,d1}, R={c0,d0}.
```

The matrices are

```
T(A,B,Q) = [[0, c], [1,-d]],
T(B,Q,R) = [[0,-c], [1,-a]],
T(Q,R,E) = [[0, 1], [-v,-z]],
T(R,E,F) = [[0, 1], [ v,-u]].
```

Forcedness gives

```
d=a=z=u=0,   c != 0,   v != 0.
```

All four new relations are flips.  New parity: `0` modulo two.

Thus every forced-preserving cross repartition preserves the old parity.

## 4. Wholesale swap

The remaining nonidentity repartition is

```
Q=D, R=C.
```

The left two new relation matrices are

```
T(A,B,D) = [[ a, c], [-b,-d]],
T(B,D,C) = [[-d, c], [-b, a]].
```

If the first is a forced identity, then `a,d` are nonzero and `b=c=0`, and
the second is also identity.  If the first is a forced flip, then `a=d=0`
and `b,c` are nonzero, and the second is also flip.  Conversely the same
conditions follow from forcedness of the second.  Hence these two relation
bits are equal.

The right two matrices are

```
T(D,C,E) = [[-u,-w], [v, z]],
T(C,E,F) = [[ z,-w], [v,-u]].
```

The identical argument shows that these two relation bits are equal.
Therefore the four new bits occur in two equal pairs and their XOR is zero.

## 5. Conclusion

After gauge normalization the old four-bit parity is zero, and every one of
the five nonidentity repartitions that preserves forcedness has new parity
zero.  Undoing the label changes proves parity conservation in the original
labelling.

Nothing in the determinant argument uses finiteness of `K`, its
characteristic, or a special property of GF(2).  The theorem therefore holds
for every field-representable rank-four local configuration.

This explains the exact GF(2), GF(3), and GF(5) certificates and upgrades them
from isolated finite evidence to regression checks of a general represented
proof.

## 6. Relation to the remaining problem

The result still stops short of the desired representation-free lemma.  The
new Lean theorem `PairCycle.crossBaseRelation_iff_mem_fundCircuit` gives a
promising route: each forced identity/flip bit can be encoded by which element
of a two-element basis lies in an outside element's fundamental circuit.  A
matroid proof reproducing the even-flip case analysis would remove the final
representability hypothesis.

Even that local theorem would not finish rank four.  The global bottleneck is
still to prove that an obstructed strict state has some legal boundary move
that creates slack or supplies the required ascent/repair mechanism.
