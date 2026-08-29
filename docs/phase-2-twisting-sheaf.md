# Phase 2 construction: the twisting sheaf

This note records the first global construction of `O(n)` on `P^1_k`.

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
- the global isomorphism `O(0) ≅ O`;
- the sheafified tensor product and multiplication maps
  `O(m) ⊗ O(n) ⟶ O(m+n)`.

The next step is to prove that the multiplication maps are isomorphisms and to
deduce the expected tensor and duality formulas. The stable local-coordinate
API keeps those results, and the later Cech calculation, insulated from the
kernel implementation.
