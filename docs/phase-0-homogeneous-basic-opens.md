# Phase 0 inventory: homogeneous basic opens

This note records the Mathlib `v4.32.1` declarations used for the standard
homogeneous basic opens of the projective line.

## Projective spectrum as a scheme

For an `ℕ`-graded commutative ring represented by a family `A : ℕ → σ` with a
`GradedRing A` instance, Mathlib's scheme is:

```lean
AlgebraicGeometry.Proj A
```

For this project:

```lean
scheme k := AlgebraicGeometry.Proj (grading k)
```

where `grading k n` is the homogeneous degree-`n` submodule of
`MvPolynomial (Fin 2) k`.

## Homogeneous basic opens

The scheme-level basic open associated to an element `f` is:

```lean
AlgebraicGeometry.Proj.basicOpen A f : (AlgebraicGeometry.Proj A).Opens
```

No homogeneity hypothesis is required to define the open. Homogeneity and
positive degree enter later when identifying the open with an affine scheme.

The standard opens are therefore represented by:

```lean
standardBasicOpen k i :=
  AlgebraicGeometry.Proj.basicOpen (grading k) (MvPolynomial.X i)
```

with `i : Fin 2`.

## Membership and elementary identities

The following declarations are available directly from Mathlib:

```lean
AlgebraicGeometry.Proj.mem_basicOpen
AlgebraicGeometry.Proj.basicOpen_one
AlgebraicGeometry.Proj.basicOpen_zero
AlgebraicGeometry.Proj.basicOpen_pow
AlgebraicGeometry.Proj.basicOpen_mul
AlgebraicGeometry.Proj.basicOpen_mono
AlgebraicGeometry.Proj.basicOpen_eq_iSup_proj
AlgebraicGeometry.Proj.isBasis_basicOpen
```

In particular:

```lean
Proj.basicOpen A (f * g) = Proj.basicOpen A f ⊓ Proj.basicOpen A g
```

will later identify the overlap of the two standard opens with
`D_+(X_0 X_1)`.

## Cover theorems

Mathlib offers two general cover criteria:

```lean
AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'
```

The first assumes the chosen elements span the irrelevant ideal. The second
assumes that the elements are homogeneous and generate the full ring as an
algebra over the degree-zero component.

For `k[X_0, X_1]`, the second criterion is the cleaner interface. The project
proves:

```lean
Algebra.adjoin (grading k 0) (Set.range (coordinate k)) = ⊤
```

by the standard induction principle `MvPolynomial.induction_on`. It then applies
`Proj.iSup_basicOpen_eq_top'` to obtain:

```lean
⨆ i : Fin 2, standardBasicOpen k i = ⊤
```

and derives the binary form:

```lean
x0BasicOpen k ⊔ x1BasicOpen k = ⊤
```

## Affine identification available for the next phase

If `f ∈ A m` and `0 < m`, Mathlib already provides:

```lean
AlgebraicGeometry.Proj.basicOpenIsoSpec
AlgebraicGeometry.Proj.basicOpenIsoAway
AlgebraicGeometry.Proj.awayι
AlgebraicGeometry.Proj.isAffineOpen_basicOpen
```

The affine coordinate ring is:

```lean
HomogeneousLocalization.Away A f
```

which is the degree-zero part of the localization away from `f`.

For intersections and pullbacks, the relevant declarations are:

```lean
AlgebraicGeometry.Proj.basicOpen_mul
AlgebraicGeometry.Proj.pullbackAwayιIso
```

These are the entry points for identifying each standard open with the affine
line and their overlap with a Laurent polynomial ring.

## Design decision

The project will use Mathlib's scheme-level `AlgebraicGeometry.Proj.basicOpen`
rather than the lower-level topological
`ProjectiveSpectrum.basicOpen`. This keeps subsequent restriction, affine-open,
and sheaf constructions in the `Scheme` API.
