# Phase 2 design: twisting objects on the projective line

This note records the first construction decision for Phase 2 and fixes the
transition-function convention used for the twisting sheaves `O(n)`.

## Construction choice

The first implementation of `O(n)` uses transition data on the bundled
standard cover

```text
U_0 = D_+(X_0),  U_1 = D_+(X_1).
```

Phase 1 identifies both charts with the affine line and identifies the overlap
with the Laurent polynomial ring `k[t,t⁻¹]`. It also proves that the two Laurent
coordinates differ by inversion.

Mathlib contains general graded-module infrastructure and the affine tilde
construction `M ↦ M̃` on `Spec R`, but the pinned version does not provide a
project-ready construction taking a shifted graded module to its associated
module sheaf on `Proj`. Building that infrastructure first would substantially
increase the scope of the initial projective-line calculation.

The transition-data construction therefore comes first. The public API remains
intrinsic enough that a future shifted-graded-module construction can be proved
isomorphic to it without changing downstream statements.

## Sign convention

On the `X_0` chart write

```text
t = X_1 / X_0.
```

For the standard local frames `e_0` and `e_1` of `O(n)`, use

```text
e_1 = t^n e_0.
```

Thus the frame transition factor is `t^n`. If a section is represented in the
two trivializations by

```text
a_0 e_0 = a_1 e_1,
```

then its coefficients satisfy

```text
a_1 = t^(-n) a_0.
```

The project records these two factors separately as

```lean
twistTransition k n
twistCoefficientTransition k n
```

so later gluing code does not have to reconstruct the sign convention.

## Identities already packaged

The transition module records:

```text
t^0 = 1
t^(m+n) = t^m t^n
t^(-n) t^n = 1
t^n t^(-n) = 1
```

and proves that every transition factor is a unit. Under the change from the
`X_0` Laurent coordinate to the `X_1` Laurent coordinate, inversion sends the
frame factor for `n` to the frame factor for `-n`.

These scalar identities support the constructions

```text
O(0) ≅ O
O(m) ⊗ O(n) ≅ O(m+n)
O(n)ᵛ ≅ O(-n).
```

All three expected formulas are now represented in the project API. The tensor
addition isomorphism is `twistingSheafTensorIso`, whose forward map is the
canonical multiplication morphism. Duality is packaged in
`TwistingSheafDuality`: `twistingSheafTensorNegIso` and
`twistingSheafNegTensorIso` give

```text
O(n) ⊗ O(-n) ≅ O,
O(-n) ⊗ O(n) ≅ O,
```

and `twistingSheafTensorInverse` records `O(-n)` as the chosen two-sided tensor
inverse of `O(n)`. Since the project-local sheafified tensor product is not yet
installed as a monoidal structure on `Scheme.Modules`, this records the
mathematical duality content directly rather than introducing an ambient
categorical `Dual` interface prematurely.

## Resulting construction

The transition data is used to construct the genuine object

```lean
twistingSheaf (k : Type u) [CommRing k] (n : ℤ) : ModuleSheaf k
```

by gluing two trivial rank-one module sheaves on the standard charts using
`twistCoefficientTransition k n` on the overlap. The implementation realizes
this gluing as a kernel expressing compatible pairs of local sections.

The resulting sheaf exposes explicit restriction isomorphisms on both standard
opens. The project additionally packages a local-to-global isomorphism
criterion for this cover. Together these support the global identification
`O(0) ≅ O` and the proof that the multiplication map is an isomorphism.

The tensor infrastructure is no longer projective-line-only: the sheafified
tensor product has been generalized to an arbitrary scheme as
`schemeModuleSheafTensor`, with left and right unit comparisons in the
projective-line specialization. For an open immersion `f : X ⟶ Y`, the project
proves both the presheaf-level tensor/restriction comparison and the sheafified
comparison

```text
restrict_f (M ⊗ N) ≅ restrict_f M ⊗ restrict_f N.
```

This comparison supplies the local proof of tensor addition. Once tensor
addition is known, the inverse exponent immediately gives the two-sided
tensor-inverse formula and completes the Phase 2 twisting-object milestone.
