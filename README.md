# Riemann-Roch in Lean

This repository develops a Lean 4 formalization of Riemann-Roch, beginning with
the projective line.

The first flagship target is

```text
chi(P^1_k, O(n)) = n + 1
```

for every field `k` and every integer `n`.

The longer road is:

```text
Riemann-Roch for P^1
  -> Riemann-Roch for smooth projective curves
  -> Hirzebruch-Riemann-Roch
  -> Grothendieck-Riemann-Roch
```

## Current milestone

The initial milestone is not yet the cohomology calculation itself. It is to
construct a clean, reusable Lean interface for:

- the scheme `P^1_k` as a `Proj`;
- its two standard affine opens;
- their coordinate rings and overlap;
- the twisting objects `O(n)`;
- the two-open Cech complex.

See `BLUEPRINT.md` for the dependency graph and progress tracker.

## Build

```bash
lake update
lake exe cache get
lake build
```

The project currently tracks Lean 4.32.1 and Mathlib 4.32.1.
