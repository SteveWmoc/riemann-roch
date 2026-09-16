# Riemann-Roch in Lean

[![CI](https://github.com/SteveWmoc/riemann-roch/actions/workflows/ci.yml/badge.svg)](https://github.com/SteveWmoc/riemann-roch/actions/workflows/ci.yml)

An experimental Lean 4 formalization of Riemann-Roch, beginning with the projective line and organized toward reusable algebraic-geometry infrastructure.

> **Project status:** active research. Phase 0 API reconnaissance, Phase 1's explicit projective-line geometry, and Phase 2's twisting-sheaf infrastructure are complete. `O(n)` is constructed globally for every integer `n`, trivialized on both standard charts, identified with the structure sheaf at `n = 0`, and equipped with canonical tensor addition isomorphisms `O(m) ⊗ O(n) ≅ O(m+n)`. The project also packages `O(-n)` as the two-sided tensor inverse of `O(n)`, giving the expected project-local duality formula. A normalized two-open Cech complex is available. The next step is Phase 3: specialize that complex to `O(n)` and compute its global sections and first cohomology. The Riemann-Roch theorem itself has not yet been formalized.

## Mathematical goal

The first flagship target is

```text
chi(P^1_k, O(n)) = n + 1
```

for every field `k` and every integer `n`.

The intended development path is:

```text
Riemann-Roch for P^1
  -> Riemann-Roch for smooth projective curves
  -> Hirzebruch-Riemann-Roch
  -> Grothendieck-Riemann-Roch
```

The project favors constructions that can later support arbitrary schemes and upstream Mathlib contributions, while using explicit coordinates where they make the first calculation tractable.

## Current development

The repository currently provides:

- the standard total-degree grading on `k[X0, X1]`;
- `P^1_k` as the `Proj` of that graded ring;
- the standard opens `D_+(X0)` and `D_+(X1)` and a proof that they cover;
- canonical affine presentations of the standard opens as spectra of degree-zero homogeneous localizations;
- the ratio coordinates `X1 / X0` and `X0 / X1` in those chart rings;
- ring equivalences from `k[t]` to both standard chart rings, sending `t` to `X1 / X0` on the first chart and to `X0 / X1` on the second, with inverses given by the corresponding dehomogenization maps;
- explicit scheme isomorphisms identifying both standard opens with the affine line `Spec k[t]`;
- Laurent-polynomial presentations of the overlap from both charts and a scheme isomorphism `D_+(X0) ∩ D_+(X1) ≅ Spec k[t,t⁻¹]`;
- an explicit Laurent transition automorphism between the two overlap coordinates, proved equal to inversion `t ↦ t⁻¹`;
- the standard two-open cover packaged as Mathlib's native `Scheme.OpenCover`, together with its affine-line components and punctured-affine-line overlap;
- the category of sheaves of modules on `P^1_k` and the structure sheaf as a module;
- a specialization of Mathlib's canonical Cech-complex functor derived from the bundled standard cover;
- a normalized two-term Cech complex for the standard cover, with differential `(s₀, s₁) ↦ s₀| - s₁|`;
- the Phase 2 transition factors for `O(n)`, with the convention `e₁ = t^n e₀`, coefficient transport by `t^(-n)`, unit identities, and compatibility with the Laurent coordinate inversion;
- the global twisting sheaf `twistingSheaf k n` for every `n : ℤ`, constructed as the kernel of the compatibility map between the two pushed-forward trivial rank-one chart modules and the overlap module;
- canonical maps from `twistingSheaf k n` to both pushed-forward trivial chart modules, their overlap equation `a₁ = t^(-n) a₀`, and a universal gluing lift for compatible local data;
- canonical trivializations of `O(n)` on both standard affine charts;
- a local-to-global criterion proving that a morphism of module sheaves is an isomorphism when its restrictions to both standard charts are isomorphisms;
- a global isomorphism `O(0) ≅ O` with the structure module;
- sheafified tensor products of module sheaves and canonical tensor addition isomorphisms `O(m) ⊗ O(n) ≅ O(m+n)`, whose forward maps are the existing coefficientwise multiplication maps;
- two-sided tensor-inverse data identifying `O(-n)` as the project-local dual of `O(n)`, with canonical isomorphisms `O(n) ⊗ O(-n) ≅ O` and `O(-n) ⊗ O(n) ≅ O`;
- left and right tensor-unit isomorphisms with the structure module;
- a scheme-general sheafified tensor product `schemeModuleSheafTensor`;
- pointwise tensor/restriction compatibility for module presheaves along open immersions;
- sheafification/restriction compatibility and the resulting isomorphism
  `restrict (M ⊗ N) ≅ restrict M ⊗ restrict N` for the scheme-general sheafified tensor product;
- design notes recording the relevant Mathlib APIs and the completed Phase 2 comparison infrastructure.

Phase 2 is complete. The tensor addition theorem is proved on both standard charts using the existing trivializations, a computation rule for the tensor-restriction comparison on pure tensors, and the standard-chart local-to-global criterion. Duality then follows from `O(n) ⊗ O(-n) ≅ O(0) ≅ O` (and similarly on the other side). Because the project-local sheafified tensor product is not yet registered as a monoidal structure on `Scheme.Modules`, the current API records this as explicit two-sided tensor-inverse data rather than an ambient categorical `Dual`. Phase 3 now begins with the explicit Cech calculation for `O(n)`.

## Repository layout

| Module or document | Contents |
| --- | --- |
| `RiemannRoch.ProjectiveLine.GradedPolynomialRing` | The coordinate ring `k[X0, X1]` and its standard grading |
| `RiemannRoch.ProjectiveLine.BasicOpens` | `P^1_k`, its standard homogeneous opens, and the cover theorem |
| `RiemannRoch.ProjectiveLine.AffineCharts` | Homogeneous-localization chart rings, open immersions, and ratio coordinates |
| `RiemannRoch.ProjectiveLine.Dehomogenization` | The `X0` polynomial chart map, dehomogenization, and chart-ring equivalence |
| `RiemannRoch.ProjectiveLine.X1Dehomogenization` | The `X1` polynomial chart map, dehomogenization, and chart-ring equivalence |
| `RiemannRoch.ProjectiveLine.AffineLineCharts` | The affine line and the scheme isomorphisms from both standard opens |
| `RiemannRoch.ProjectiveLine.Overlap` | The Laurent-polynomial overlap ring, both chart localizations, and the punctured-affine-line isomorphism |
| `RiemannRoch.ProjectiveLine.OverlapTransition` | Reciprocal overlap coordinates and the Laurent inversion transition map |
| `RiemannRoch.ProjectiveLine.StandardCover` | The bundled `Scheme.OpenCover`, affine chart components, and overlap presentation |
| `RiemannRoch.ProjectiveLine.SheavesAndCech` | Module sheaves and the canonical Cech complex derived from the bundled cover |
| `RiemannRoch.ProjectiveLine.NormalizedCech` | The normalized two-term Cech complex on the standard cover |
| `RiemannRoch.ProjectiveLine.TwistingTransition` | Laurent frame and coefficient transition factors for the twisting sheaves `O(n)` |
| `RiemannRoch.ProjectiveLine.TwistingSheaf` | Global twisting sheaves as kernels of the two-chart overlap compatibility maps |
| `RiemannRoch.ProjectiveLine.TwistingSheafCoordinates` | Canonical chart components, overlap compatibility, and the universal gluing lift for `O(n)` |
| `RiemannRoch.ProjectiveLine.TwistingSheafRestrictions` | The `X0`-chart trivialization of `O(n)` |
| `RiemannRoch.ProjectiveLine.TwistingSheafX1Trivialization` | The `X1`-chart trivialization of `O(n)` |
| `RiemannRoch.ProjectiveLine.TwistingSheafZero` | The global identification `O(0) ≅ O` |
| `RiemannRoch.ProjectiveLine.StandardChartIso` | Local-to-global isomorphism detection on the two standard charts |
| `RiemannRoch.ProjectiveLine.TwistingSheafMultiplication` | Sheafified tensor products and the maps `O(m) ⊗ O(n) ⟶ O(m+n)` |
| `RiemannRoch.ProjectiveLine.TensorUnit` | Left and right unit isomorphisms for the sheafified tensor product |
| `RiemannRoch.ProjectiveLine.TensorRestriction` | Scheme-general tensor construction and presheaf-level compatibility with open restriction |
| `RiemannRoch.ProjectiveLine.TensorRestrictionSheafification` | Sheafification/restriction compatibility and the sheafified tensor restriction isomorphism |
| `RiemannRoch.ProjectiveLine.TwistingSheafTensorIso` | The canonical tensor addition isomorphisms `O(m) ⊗ O(n) ≅ O(m+n)` |
| `RiemannRoch.ProjectiveLine.TwistingSheafDuality` | Two-sided tensor-inverse data realizing the project-local duality `O(n)ᵛ ≅ O(-n)` |
| `RiemannRoch.ProjectiveLine.Target` | Integration boundary and projective-line theorem target |
| `RiemannRoch` | Main import file exporting the public development |
| [`BLUEPRINT.md`](BLUEPRINT.md) | Detailed phased roadmap and progress tracker |
| [`docs/`](docs/) | API inventories and design notes, including the Phase 2 twisting-sheaf and tensor-restriction constructions |

## Quick start

The exact Lean and Mathlib versions are pinned by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

```sh
git clone https://github.com/SteveWmoc/riemann-roch.git
cd riemann-roch
lake build
```

To use the full public development from another Lean file:

```lean
import RiemannRoch
```
