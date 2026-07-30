# Phase 0 inventory: sheaves of modules and Cech infrastructure

This note records the Mathlib `v4.32.1` declarations relevant to sheaves of
modules on `P^1_k`, the standard two-open Cech complex, and abstract sheaf
cohomology.

## The category of module sheaves on a scheme

For a scheme `X`, Mathlib defines

```lean
X.Modules := SheafOfModules X.ringCatSheaf
```

in `Mathlib.AlgebraicGeometry.Modules.Sheaf`.

This is the category of sheaves of modules over the structure sheaf. Mathlib
provides the instances

```lean
Abelian X.Modules
HasLimits X.Modules
HasColimits X.Modules
```

so kernels, cokernels, exact sequences, products, coproducts, and homological
algebra are available in the expected category.

For `M : X.Modules`, the principal section-level interface is

```lean
Scheme.Modules.presheaf M
Scheme.Modules.Hom.app
Scheme.Modules.isSheaf M
```

and the scoped notation

```lean
Γ(M, U)
```

denotes the abelian group of sections of `M` on `U : X.Opens`. It carries a
canonical module structure over `Γ(X, U)`. Restriction maps respect scalar
multiplication.

## Structure sheaf and functoriality

The structure sheaf regarded as a module over itself is

```lean
SheafOfModules.unit X.ringCatSheaf
```

For a scheme morphism `f : X ⟶ Y`, Mathlib supplies

```lean
Scheme.Modules.pullback f
Scheme.Modules.pushforward f
Scheme.Modules.pullbackPushforwardAdjunction f
```

For an open immersion it also supplies restriction machinery, including

```lean
Scheme.Modules.restrict
Scheme.Modules.restrictFunctor
Scheme.Modules.restrictAppIso
Scheme.Modules.restrictUnitIso
```

These will be the natural interfaces for restricting `O(n)` to the two standard
opens.

## Quasi-coherent and locally free module sheaves

Mathlib defines properties on sheaves of modules:

```lean
SheafOfModules.IsQuasicoherent M
SheafOfModules.IsLocallyFree M
```

Quasi-coherence is expressed by local presentations as cokernels of maps
between free sheaves. Locally free sheaves are automatically quasi-coherent.
The relevant files are

```text
Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
```

On an affine scheme, an ordinary module produces a module sheaf through

```lean
AlgebraicGeometry.tilde M : (Spec R).Modules
```

with accompanying functoriality and localization results on principal opens.
In particular, `tilde.isoTop` identifies the original module with the global
sections of its associated sheaf. This will be useful after each standard open
of `P^1_k` is identified with an affine line.

## Forgetting to abelian sheaves and abstract cohomology

Mathlib's abstract sheaf cohomology is defined for sheaves of abelian groups.
The bridge from an `O_X`-module is

```lean
SheafOfModules.toSheaf X.ringCatSheaf
```

which forgets the module structure while retaining the sheaf condition.
Abstract cohomology is then

```lean
CategoryTheory.Sheaf.H F n
```

where `F` is the underlying abelian sheaf. Internally this is an `Ext` group
from the constant sheaf associated to `ULift ℤ`.

The project packages this route as

```lean
underlyingAbelianSheaf M
abstractCohomology M n
```

## General Cech-complex infrastructure

Mathlib defines

```lean
CategoryTheory.cechComplexFunctor U
```

for a family `U : ι → C` in a category with finite products. Its type is
conceptually

```lean
(Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ
```

for a preadditive target category `A` with products.

In degree `n`, the complex is a product indexed by all functions

```lean
Fin (n + 1) → ι
```

of the value of the presheaf on the corresponding finite product of members of
`U`. For the category of opens of a topological space, these finite products
are intersections.

The construction factors through:

```lean
FormalCoproduct.cech
FormalCoproduct.cochainComplexFunctor
AlgebraicTopology.alternatingCofaceMapComplex
```

The project specializes this construction to the standard family

```lean
standardBasicOpen k : Fin 2 → (scheme k).Opens
```

and defines

```lean
standardCechComplexFunctor k
standardCechComplex M
```

for `M : (scheme k).Modules`.

## Important limitation: the complex is unnormalized

The indexing by all functions `Fin (n + 1) → Fin 2` permits repeated indices.
Consequently, the canonical Mathlib complex is the unnormalized alternating
coface complex. Even for a two-open cover, it has terms in every nonnegative
degree; it is not definitionally the familiar two-term complex

```text
Γ(U_0, M) × Γ(U_1, M)  ⟶  Γ(U_0 ∩ U_1, M).
```

Mathlib contains general normalized-complex and Dold-Kan infrastructure, but
there is not currently a project-ready wrapper turning this particular Cech
object into the explicit two-term complex needed for our calculation.

## Important limitation: no Cech-to-derived comparison is packaged

`CategoryTheory.Sheaf.H` and `CategoryTheory.cechComplexFunctor` are presently
separate constructions. The inventoried API does not provide a theorem that
the cohomology of this Cech complex agrees with abstract sheaf cohomology, nor
a scheme-specific acyclic-cover theorem for quasi-coherent sheaves on affine
opens.

For the project, these must be treated as distinct goals:

1. compute an explicit normalized two-open complex;
2. compare it with Mathlib's canonical unnormalized Cech complex;
3. prove that the resulting Cech cohomology agrees with abstract sheaf
   cohomology for the sheaves and cover under consideration.

## Design decision

The project will retain `standardCechComplex M` as the canonical Mathlib-backed
Cech object. For the concrete calculation on `P^1`, it will probably also define
a project-local normalized two-term complex and a comparison map.

This separates the elementary Laurent-polynomial calculation from the deeper
comparison theorem. The likely upstream contributions are:

- a scheme/open-cover wrapper around `cechComplexFunctor`;
- a normalized finite-cover Cech complex with convenient formulas;
- comparison maps between normalized and unnormalized Cech complexes;
- an acyclic-cover theorem comparing Cech cohomology with `Sheaf.H`.
