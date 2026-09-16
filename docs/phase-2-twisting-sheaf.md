# Phase 2 construction: the twisting sheaf

This note records the first global construction of `O(n)` on `P^1_k` and the
public infrastructure built around it.

## Construction

Let

```text
U_0 = D_+(X_0),
U_1 = D_+(X_1),
W   = U_0 ∩ U_1.
```

Each chart carries the trivial rank-one module sheaf. These are pushed forward
to `P^1_k`. The overlap also carries the trivial rank-one module sheaf, pushed
forward along `W -> P^1_k`.

The chart-to-overlap maps are built from Mathlib's restriction/pushforward
adjunction for open immersions. The restriction of the structure sheaf is
identified with the structure sheaf of the smaller open via
`Scheme.Modules.restrictUnitIso`.

With the convention

```text
e_1 = t^n e_0,
```

coefficients satisfy

```text
a_1 = t^(-n) a_0.
```

The Laurent polynomial `t^(-n)` is transported to a global section of the
structure sheaf on `W` through the explicit isomorphism

```text
W ≅ Spec k[t,t^-1].
```

Via `SheafOfModules.unitHomEquiv`, this section defines multiplication by
`t^(-n)` on the trivial overlap module.

The compatibility morphism is therefore

```text
j_{0*} O_{U_0} ⊞ j_{1*} O_{U_1} -> j_{W*} O_W,
(a_0, a_1) |-> t^(-n) a_0 - a_1.
```

The project defines

```lean
twistingSheaf k n
```

as the kernel of this morphism in the abelian category `(scheme k).Modules`.

## Public interface

The implementation exposes:

- the overlap inclusions into the two standard charts;
- the Laurent-to-overlap-section map;
- multiplication by the coefficient transition factor on the overlap module;
- the two chart restriction maps after pushforward;
- the compatibility morphism;
- `twistingSheaf k n` and its canonical kernel inclusion;
- the two local-coordinate projections, their overlap equation, and a universal
  gluing lift;
- trivializations on both standard affine charts;
- `isIso_of_standard_chart_restrictions`, which upgrades isomorphisms on both
  standard-chart restrictions to a global isomorphism;
- the global isomorphism `O(0) ≅ O`;
- the sheafified tensor product and canonical multiplication isomorphisms
  `O(m) ⊗ O(n) ≅ O(m+n)`;
- two-sided tensor-inverse data identifying `O(-n)` as the project-local dual of
  `O(n)`, with `O(n) ⊗ O(-n) ≅ O` and `O(-n) ⊗ O(n) ≅ O`;
- left and right tensor-unit isomorphisms with the structure module;
- the scheme-general tensor construction `schemeModuleSheafTensor`;
- the presheaf-level tensor/restriction comparison for open immersions;
- the sheafification/restriction comparison and the resulting public
  `restrictSchemeModuleSheafTensorIso`.

## Completed tensor and duality strategy

The global multiplication map is proved to be an isomorphism in
`TwistingSheafTensorIso.lean` by a local argument:

1. restrict the multiplication map to `U_0` and `U_1`;
2. use `restrictSchemeModuleSheafTensorIso` to commute restriction past the
   sheafified tensor product;
3. identify both restricted twisting sheaves with the trivial rank-one module
   through the existing chart trivializations;
4. reduce the restricted multiplication map to the evident multiplication map
   on a trivial rank-one module;
5. apply `isIso_of_standard_chart_restrictions` to conclude globally.

The restriction computation and coefficient formulas are described in
[the tensor restriction note](phase-2-tensor-restriction.md).

Duality then requires no second local calculation. Substituting `-n` into the
tensor-addition theorem gives

```text
O(n) ⊗ O(-n) ≅ O(0) ≅ O,
O(-n) ⊗ O(n) ≅ O(0) ≅ O.
```

`TwistingSheafDuality.lean` packages these isomorphisms and records `O(-n)` as
the chosen two-sided tensor inverse of `O(n)`. The project-local tensor product
is not yet registered as a monoidal structure on `Scheme.Modules`, so this is
the appropriate present form of the expected formula `O(n)ᵛ ≅ O(-n)`.

This completes Phase 2. The next mathematical work is the explicit normalized
Cech calculation for `O(n)` in Phase 3.
