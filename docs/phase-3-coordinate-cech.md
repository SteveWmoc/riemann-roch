# Phase 3 coordinate Cech complex

The normalized standard-cover Cech complex already exists for an arbitrary
module sheaf on `P^1_k`. For the twisting sheaf `O(n)`, Phase 3 now introduces
the explicit algebraic complex that will be used for the cohomology calculation.

Write

```text
t = X1 / X0
u = X0 / X1 = t^-1.
```

The chosen local frames satisfy

```text
e1 = t^n e0,
```

so coefficient transport from the `X0` frame to the `X1` frame is
multiplication by `t^(-n)`.

## Coordinate differential

The degree-zero and degree-one terms are

```text
C^0 = k[t] ⊕ k[u]
C^1 = k[t,t^-1].
```

Using the `X0` Laurent coordinate on the target, the two restriction maps are

```text
p(t) |-> p(t) t^(-n)
q(u) |-> q(t^-1).
```

Hence the differential is

```text
d_n(p,q) = p(t) t^(-n) - q(t^-1).
```

In Lean these are exposed as

```lean
twistingCechX0CoordinateRestriction
twistingCechX1CoordinateRestriction
twistingCechCoordinateDifferential
twistingCechCoordinateComplex
```

The complex is concentrated in degrees zero and one, matching the existing
normalized sheaf-theoretic complex.

## Deliberate boundary

This slice does not yet identify the coordinate complex with

```lean
standardNormalizedCechComplex (twistingSheaf k n)
```

as a cochain complex. That comparison is the next Phase 3 step. It will use the
two chart trivializations of `O(n)`, the Laurent presentation of the overlap,
and the already-fixed coefficient transition convention.

Once the comparison is established, the cohomology calculation becomes an
explicit kernel/cokernel problem for `d_n`. In particular:

- `H^0` is the kernel of `d_n`;
- `H^1` is the cokernel of `d_n`;
- all higher groups vanish in the normalized complex.

This separation is intentional: the Laurent-polynomial algebra can be developed
and tested independently of the sheaf-restriction plumbing.
