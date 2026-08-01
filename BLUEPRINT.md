# Blueprint

## Flagship target

For a field `k` and an integer `n`, formalize

```text
chi(P^1_k, O(n)) = n + 1.
```

The proof should be organized so that its constructions remain useful for
Riemann-Roch on arbitrary smooth projective curves and, eventually,
Grothendieck-Riemann-Roch.

Status legend:

- `[ ]` not started
- `[~]` in progress
- `[x]` complete
- `[?]` blocked by an unresolved API or mathematical design decision

## Phase 0: Repository and API reconnaissance

- [x] Pin Lean and Mathlib versions.
- [x] Add a minimal library root.
- [x] Add GitHub Actions CI.
- [x] Verify that `Proj` and abstract sheaf cohomology can be imported together.
- [x] Inventory the exact Mathlib definitions needed for graded polynomial rings.
- [x] Inventory the exact Mathlib definitions for homogeneous basic opens.
- [x] Inventory available sheaves of modules and Cech-complex infrastructure.
- [x] Record gaps that are likely to belong upstream in Mathlib.

### Exit criterion

Focused design notes identify the exact Lean types and declarations that will
represent every object in the first geometric milestone, together with the
principal API gaps.

## Phase 1: The projective line

- [x] Construct the standard grading on `k[X0, X1]`.
- [x] Define a project-local abbreviation for `P^1_k = Proj k[X0, X1]`.
- [x] Define the homogeneous coordinates `X0` and `X1`.
- [x] Define the basic opens `D_+(X0)` and `D_+(X1)`.
- [x] Prove `D_+(X0) sup D_+(X1) = top`.
- [x] Package the canonical affine presentation
      `D_+(X_i) = Spec ((k[X0, X1]_(X_i))_0)`.
- [x] Construct the map `k[t] -> (k[X0, X1]_(X0))_0`, its dehomogenization
      left inverse, and prove injectivity.
- [ ] Prove surjectivity and package the `X0` chart-ring equivalence.
- [ ] Construct the corresponding `X1` chart-ring equivalence.
- [ ] Compose the ring and scheme isomorphisms to identify each standard open
      with an affine line.
- [ ] Identify the overlap with the Laurent polynomial coordinate ring.
- [ ] Package the standard two-open cover as a reusable object.

### Exit criterion

Lean has a usable `P^1_k` with its standard affine cover and explicit
coordinate-ring descriptions.

## Phase 2: Twisting objects

- [ ] Decide whether to construct `O(n)` first from shifted graded modules or by
      transition data on the standard cover.
- [ ] Define `O(n)` for every integer `n`.
- [ ] Prove `O(0)` is the structure sheaf.
- [ ] Construct multiplication maps `O(m) tensor O(n) -> O(m+n)`.
- [ ] Prove the expected tensor and duality isomorphisms.
- [ ] Prove restriction formulas on the two standard opens.

### Exit criterion

The family `O(n)` is available through a stable public API, with enough
restriction data for an explicit Cech calculation.

## Phase 3: The two-open Cech calculation

- [ ] Construct a normalized project-local two-open Cech complex.
- [ ] Construct the degree-zero Cech differential.
- [ ] Construct the degree-one Cech differential.
- [ ] Identify global sections for `n >= 0`.
- [ ] Prove vanishing of global sections for `n < 0`.
- [ ] Compute first cohomology for all integers `n`.
- [ ] Prove vanishing above degree one for the normalized complex.
- [ ] Compare the normalized complex with Mathlib's canonical unnormalized
      `standardCechComplex`.
- [ ] Reconcile Cech cohomology with Mathlib's abstract sheaf cohomology.

### Expected dimension formulas

```text
dim H^0(P^1, O(n)) = n + 1       for n >= 0
dim H^0(P^1, O(n)) = 0           for n < 0

dim H^1(P^1, O(n)) = 0           for n >= -1
dim H^1(P^1, O(n)) = -n - 1      for n <= -2
```

### Exit criterion

For every integer `n`, Lean knows the dimensions of `H^0` and `H^1` of `O(n)`.

## Phase 4: Riemann-Roch on the projective line

- [ ] Define the Euler characteristic in the finite-dimensional bounded case.
- [ ] Prove `chi(P^1_k, O(n)) = n + 1`.
- [ ] Derive the divisor formulation on `P^1`.
- [ ] Document which parts should be proposed for inclusion in Mathlib.

### Exit criterion

The flagship theorem is proved without `sorry`.

## Phase 5: Curves

- [ ] Formalize the divisor-line-bundle correspondence needed for curves.
- [ ] Define degree for divisors and line bundles.
- [ ] Develop skyscraper sheaves at closed points.
- [ ] Prove additivity of Euler characteristic in short exact sequences.
- [ ] Prove the point-twisting increment formula.
- [ ] Prove Riemann-Roch for line bundles on smooth projective curves.
- [ ] Add Serre duality and derive the classical divisor formula.

## Phase 6: Toward Grothendieck-Riemann-Roch

- [ ] Develop coherent-sheaf `K_0`.
- [ ] Define pushforward on `K_0` through derived direct image.
- [ ] Develop Chern classes and the Chern character.
- [ ] Develop Chow groups and proper pushforward.
- [ ] Define Todd classes.
- [ ] Prove Hirzebruch-Riemann-Roch.
- [ ] State and prove Grothendieck-Riemann-Roch for a carefully chosen first
      class of morphisms.

## Design principles

1. Every phase must produce reusable library infrastructure.
2. Prefer intrinsic objects over coordinate-specific encodings, but use explicit
   coordinates when they make the first calculation tractable.
3. Separate project-local experimentation from code suitable for upstreaming.
4. Open small pull requests with one coherent mathematical purpose.
5. Keep the main branch compiling and free of `sorry`.
6. Record API discoveries and blockers instead of hiding them in abandoned
   scratch files.
