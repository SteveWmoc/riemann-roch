# Phase 2 design: twisting objects on the projective line

This note records the first construction decision for Phase 2 and fixes the
transition-function convention used for the twisting sheaves `O(n)`.

## Construction choice

The first implementation of `O(n)` will use transition data on the bundled
standard cover

```text
U_0 = D_+(X_0),  U_1 = D_+(X_1).
```

Phase 1 already identifies both charts with the affine line and identifies the
overlap with the Laurent polynomial ring `k[t,t⁻¹]`. It also proves that the two
Laurent coordinates differ by inversion.

Mathlib contains general graded-module infrastructure and the affine tilde
construction `M ↦ M̃` on `Spec R`, but the pinned version does not provide a
project-ready construction taking a shifted graded module to its associated
module sheaf on `Proj`. Building that infrastructure first would substantially
increase the scope of the initial projective-line calculation.

The transition-data construction therefore comes first. The public API should
remain intrinsic enough that a future shifted-graded-module construction can be
proved isomorphic to it without changing downstream statements.

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

These are the scalar identities needed for the later constructions

```text
O(0) ≅ O
O(m) ⊗ O(n) ≅ O(m+n)
O(n)ᵛ ≅ O(-n).
```

## Next construction

The next milestone is a genuine object

```lean
twistingSheaf (k : Type u) [CommRing k] (n : ℤ) : ModuleSheaf k
```

obtained by gluing two trivial rank-one module sheaves on the standard charts
using `twistCoefficientTransition k n` on the overlap. A convenient categorical
realization is expected to use a kernel/equalizer expressing compatible pairs
of local sections.

The resulting sheaf should expose explicit restriction isomorphisms on the two
standard opens; those formulas are the interface needed by the normalized Cech
calculation in Phase 3.
