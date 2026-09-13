# Phase 2 infrastructure: tensor products and open restriction

This note records the comparison infrastructure completed after the first
construction of the twisting-sheaf multiplication maps. Its purpose is to make
local proofs about the sheafified tensor product usable on the two standard
affine charts of `P^1_k`.

## Why this comparison is needed

The project defines multiplication maps

```text
O(m) ⊗ O(n) ⟶ O(m+n).
```

The intended proof that these maps are isomorphisms is local on the standard
cover. That requires a canonical way to identify the restriction of a tensor
product with the tensor product of the restrictions. The project-local tensor
product, however, is defined by sheafifying a pointwise tensor product of module
presheaves, so two separate compatibility problems have to be solved:

1. pointwise tensor product versus restriction;
2. sheafification versus restriction.

Both are now packaged.

## Scheme-general tensor product

The sheafified tensor construction was generalized from `P^1_k` to an arbitrary
scheme:

```lean
schemeModuleSheafTensor
    (X : Scheme) (M N : X.Modules) : X.Modules
```

It is defined by sheafifying the project-local pointwise tensor product of the
underlying module presheaves. The original projective-line construction remains
definitionally the specialization to `scheme k`:

```lean
moduleSheafTensor_eq_schemeModuleSheafTensor
```

This lets the restriction theorem be stated once for arbitrary open immersions
rather than separately for the two standard charts.

## Presheaf-level restriction

For an open immersion `f : X ⟶ Y`, Mathlib's scheme-module restriction functor
is represented on underlying module presheaves by precomposition with the opens
functor together with restriction of scalars along the canonical ring
isomorphisms on sections.

The project first proves that restriction of scalars along a ring equivalence
has an invertible lax-monoidal tensorator. Componentwise, this gives the
canonical isomorphism comparing

```text
(restrict M) ⊗ (restrict N)
```

with the restriction of the pointwise tensor product. The resulting presheaf
isomorphism is exposed as

```lean
restrictModulePresheafTensorIso
```

in `RiemannRoch.ProjectiveLine.TensorRestriction`.

## Sheafification versus restriction

The remaining issue is that the sheafified tensor product applies
`PresheafOfModules.sheafification` after the pointwise tensor construction.
Restriction must therefore commute with that sheafification step as well.

The proof uses Mathlib's generic compatibility between continuous pushforward
and sheafification. After forgetting a module sheaf to its underlying sheaf of
abelian groups, the project identifies the canonical module-level comparison
with Mathlib's

```lean
Functor.pushforwardContinuousSheafificationCompatibility
```

for the opens functor induced by the open immersion. Since the underlying map
is an isomorphism and the forgetful functor reflects isomorphisms, the
module-level comparison is an isomorphism.

This argument is implemented in
`RiemannRoch.ProjectiveLine.TensorRestrictionSheafification`.

## Final public comparison

The two stages compose to give

```lean
restrictSchemeModuleSheafTensorIso
```

with shape

```text
restrict_f (schemeModuleSheafTensor Y M N)
  ≅
schemeModuleSheafTensor X (restrict_f M) (restrict_f N).
```

This is the Phase 2 bridge needed by the twisting-sheaf multiplication proof.
For `f` equal to either standard-chart open immersion, it moves the global
tensor product into a form where the existing chart trivializations can be
applied directly.

## Interaction with the local-to-global criterion

The project also provides

```lean
isIso_of_standard_chart_restrictions
```

which proves that a morphism of module sheaves on `P^1_k` is an isomorphism if
its restrictions to both standard charts are isomorphisms.

Together, the intended proof of

```text
O(m) ⊗ O(n) ≅ O(m+n)
```

is now structurally straightforward:

1. restrict the canonical multiplication map to each standard chart;
2. commute restriction with tensor using
   `restrictSchemeModuleSheafTensorIso`;
3. rewrite the three twisting sheaves using their chart trivializations;
4. prove the resulting rank-one multiplication map is an isomorphism;
5. conclude globally with `isIso_of_standard_chart_restrictions`.

No further general restriction/sheafification infrastructure is expected to be
needed for that theorem.
