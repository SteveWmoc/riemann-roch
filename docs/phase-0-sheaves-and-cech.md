# Phase 0 inventory: sheaves of modules and Cech infrastructure

This note began as an inventory of the Mathlib `v4.32.1` declarations relevant
to sheaves of modules on `P^1_k`, the standard two-open Cech complex, and
abstract sheaf cohomology. The repository now targets Lean/Mathlib 4.33.1.
The project code using the interfaces below has been ported to that pin; the
historical limitations are retained here, with the project-local infrastructure
added since the original survey recorded separately.

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

These are now used throughout Phase 2. In particular, the project packages
explicit chart trivializations of `O(n)`, a local-to-global isomorphism
criterion on the two standard charts, and tensor/restriction comparison
isomorphisms for open immersions.

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
sections of its associated sheaf. This remains useful after each standard open
of `P^1_k` is identified with an affine line.

## Forgetting to abelian sheaves and abstract cohomology

Mathlib's abstract sheaf cohomology is defined for sheaves of abelian groups.
The bridge from an `O_X`-module is

```lean
SheafOfModules.toSheaf X.ringCatSheaf
```

which forgets the module structure while retaining the sheaf condition. The
project packages this bridge as

```lean
underlyingAbelianSheaf M
```

Abstract cohomology is then expressed by

```lean
CategoryTheory.Sheaf.H F n
```

where `F` is the underlying abelian sheaf. Internally this is an `Ext` group
from the constant sheaf associated to `ULift ℤ`.

The declaration `Sheaf.H` has explicit `HasSheafify` and `HasExt` requirements.
A direct project abbreviation for

```lean
Sheaf.H (underlyingAbelianSheaf M) n
```

was tested during the original inventory. Typeclass search reached the
derived-category localization requirement `Localization.HasSmallLocalizedHom`
and did not synthesize within the default heartbeat budget. We therefore expose
the forgetful bridge but still do not conceal the derived-category requirements
behind a project abbreviation. Establishing a stable scheme-module cohomology
wrapper remains a later infrastructure task.

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

The project specializes this construction to the family of ranges of the
bundled standard cover

```lean
standardOpenCover k
```

and defines

```lean
standardCoverOpens k
standardCechComplexFunctor k
standardCechComplex M
```

for `M : (scheme k).Modules`. The target category and universe are stated
explicitly as `AddCommGrpCat.{u}` so typeclass inference recognizes the
required preadditive and product instances.

## The canonical Cech complex is unnormalized

The indexing by all functions `Fin (n + 1) → Fin 2` permits repeated indices.
Consequently, the canonical Mathlib complex is the unnormalized alternating
coface complex. Even for a two-open cover, it has terms in every nonnegative
degree; it is not definitionally the familiar two-term complex

```text
Γ(U_0, M) × Γ(U_1, M)  ⟶  Γ(U_0 ∩ U_1, M).
```

This was an important Phase 0 gap. The project has since filled the concrete
side of that gap with `RiemannRoch.ProjectiveLine.NormalizedCech`, which defines
a project-local normalized complex concentrated in degrees zero and one, with
the expected difference-of-restrictions differential and vanishing above
one. The remaining task is not to construct the normalized complex, but to
compare it formally with Mathlib's canonical unnormalized Cech complex.

## Important limitation: no Cech-to-derived comparison is packaged

`CategoryTheory.Sheaf.H` and `CategoryTheory.cechComplexFunctor` remain separate
constructions in the interfaces used by this project. We do not currently have
a project theorem identifying the cohomology of the explicit normalized Cech
complex with abstract sheaf cohomology, nor a scheme-specific acyclic-cover
theorem specialized to the standard affine cover.

For the project, the remaining comparison goals are:

1. compute the explicit normalized two-open complex for `O(n)`;
2. compare the normalized complex with Mathlib's canonical unnormalized Cech
   complex;
3. establish the derived-category instances needed to use `Sheaf.H` reliably;
4. prove that the resulting Cech cohomology agrees with abstract sheaf
   cohomology for the sheaves and cover under consideration.

## Current project-local layer

The original inventory deliberately avoided inventing wrappers before the
geometry was understood. The project now contains both sides needed for the
concrete computation:

- `standardCechComplex M`, backed directly by Mathlib's `cechComplexFunctor`;
- a normalized two-term project-local complex for the standard cover;
- explicit standard-chart and overlap coordinate rings;
- global twisting sheaves with chart trivializations.

This keeps the elementary polynomial/Laurent-polynomial calculation separate
from the deeper comparison theorem. Likely reusable or upstream-facing work
still includes:

- a normalized finite-cover Cech complex with convenient general formulas;
- comparison maps between normalized and unnormalized Cech complexes;
- an ergonomic scheme-module interface to derived sheaf cohomology;
- an acyclic-cover theorem comparing Cech cohomology with `Sheaf.H`.
