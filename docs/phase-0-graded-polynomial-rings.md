# Phase 0 inventory: graded polynomial rings

This note records the Mathlib `v4.32.1` declarations chosen to represent the
standard graded coordinate ring of the projective line.

## Chosen representation

For a coefficient ring `k`, use

```lean
MvPolynomial (Fin 2) k
```

for `k[X0, X1]`. The variable index type is `Fin 2`, so the two homogeneous
coordinates are `MvPolynomial.X (0 : Fin 2)` and
`MvPolynomial.X (1 : Fin 2)`.

The standard total-degree grading is the family

```lean
fun n : ℕ => MvPolynomial.homogeneousSubmodule (Fin 2) k n
```

of `k`-submodules of `MvPolynomial (Fin 2) k`.

## Minimal imports

The grading API is exported by

```lean
import Mathlib.RingTheory.MvPolynomial.Homogeneous
```

Construction of `Proj` and its homogeneous basic opens additionally needs

```lean
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
```

The project should import both explicitly rather than rely on transitive
imports.

## Core polynomial declarations

| Mathematical object | Mathlib declaration | Lean type or role |
| --- | --- | --- |
| Polynomial ring `k[X_i]` | `MvPolynomial σ k` | Abbreviation for `AddMonoidAlgebra k (σ →₀ ℕ)` |
| Exponent vector | `σ →₀ ℕ` | A finitely supported function of exponents |
| Monomial `a X^s` | `MvPolynomial.monomial s a` | `monomial s : k →ₗ[k] MvPolynomial σ k` |
| Constant polynomial | `MvPolynomial.C` | `k →+* MvPolynomial σ k` |
| Variable `X_i` | `MvPolynomial.X i` | Element of `MvPolynomial σ k` |
| Coefficient | `MvPolynomial.coeff s p` | Coefficient of exponent vector `s` in `p` |
| Polynomial support | `p.support` | Finite set of exponent vectors with nonzero coefficient |
| Total degree | `p.totalDegree` | Maximum total degree of a monomial in `p` |
| Monomial degree | `Finsupp.degree s` | Sum of the entries of exponent vector `s` |

## Homogeneity declarations

| Purpose | Mathlib declaration |
| --- | --- |
| Predicate that `p` is homogeneous of degree `n` | `MvPolynomial.IsHomogeneous p n` |
| Degree-`n` submodule | `MvPolynomial.homogeneousSubmodule σ k n` |
| Membership simplification | `MvPolynomial.mem_homogeneousSubmodule` |
| Constants have degree zero | `MvPolynomial.isHomogeneous_C` |
| Variables have degree one | `MvPolynomial.isHomogeneous_X` |
| Products add degrees | `MvPolynomial.IsHomogeneous.mul` |
| Powers multiply degrees | `MvPolynomial.IsHomogeneous.pow` |
| Degree-zero piece is the constants | `MvPolynomial.homogeneousSubmodule_zero` |
| Degree-one piece is spanned by the variables | `MvPolynomial.homogeneousSubmodule_one_eq_span_X` |
| Degree-`n` piece is the `n`th power of the degree-one piece | `MvPolynomial.homogeneousSubmodule_one_pow` |

## Decomposition and projections

Mathlib already proves that every multivariate polynomial is the finite sum of
its homogeneous components.

| Purpose | Mathlib declaration |
| --- | --- |
| Projection onto degree `n` | `MvPolynomial.homogeneousComponent n` |
| Projection lands in degree `n` | `MvPolynomial.homogeneousComponent_mem` |
| Coefficient formula for a projection | `MvPolynomial.coeff_homogeneousComponent` |
| Reconstruction from components | `MvPolynomial.sum_homogeneousComponent` |
| Internal direct-sum decomposition | `MvPolynomial.decomposition` |
| Component formula for the decomposition | `MvPolynomial.decomposition.decompose'_apply` |

The generic API behind this is:

- `GradedRing 𝒜` for an internally graded ring;
- `GradedAlgebra 𝒜`, an abbreviation for `GradedRing` when the pieces are
  submodules;
- `DirectSum.decomposeAlgEquiv 𝒜` for the algebra equivalence with the direct
  sum of homogeneous pieces;
- `GradedAlgebra.proj 𝒜 n` for the generic degree-`n` projection.

For multivariate polynomials, the specialized
`MvPolynomial.homogeneousComponent` is preferable in polynomial-specific
proofs.

## Critical instance decision

The standard grading is supplied by

```lean
MvPolynomial.gradedAlgebra
```

with type

```lean
GradedAlgebra (MvPolynomial.homogeneousSubmodule σ k)
```

This is deliberately **not** a global instance, because Mathlib also supports
weighted gradings on the same polynomial ring. Our project must install it
locally or define a project-local instance with an explicit expected type.

Chosen pattern:

```lean
local instance (k : Type*) [CommRing k] :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin 2) k) :=
  MvPolynomial.gradedAlgebra
```

A later project-local abbreviation may hide the full family name, but the
underlying Mathlib grading should remain definitionally visible whenever
possible.

## Interface with `Proj`

`AlgebraicGeometry.Proj` accepts a family `𝒜 : ℕ → σ` of additive subgroups of
a commutative ring, together with `[GradedRing 𝒜]`. Taking

```lean
𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k
```

and installing `MvPolynomial.gradedAlgebra` therefore supplies exactly the
input required for

```lean
AlgebraicGeometry.Proj 𝒜
```

No custom grading construction is required.

The next inventory should identify the declarations for
`AlgebraicGeometry.Proj.basicOpen`, the two opens associated to `X0` and `X1`,
and the theorem best suited to proving that they cover the projective line.

## Project-local names to introduce

The first implementation file should introduce only thin aliases:

```lean
abbrev Variable := Fin 2
abbrev CoordinateRing (k : Type*) [CommRing k] := MvPolynomial Variable k
abbrev grading (k : Type*) [CommRing k] :
    ℕ → Submodule k (CoordinateRing k) :=
  MvPolynomial.homogeneousSubmodule Variable k
```

It should then install the graded-algebra instance and define `x0` and `x1`.
The actual `Proj` abbreviation may be introduced either in the same file or in
the following homogeneous-basic-open milestone, depending on which import
boundary gives the cleanest API.
