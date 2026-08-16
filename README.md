# Riemann-Roch in Lean

[![CI](https://github.com/SteveWmoc/riemann-roch/actions/workflows/ci.yml/badge.svg)](https://github.com/SteveWmoc/riemann-roch/actions/workflows/ci.yml)

An experimental Lean 4 formalization of Riemann-Roch, beginning with the projective line and organized toward reusable algebraic-geometry infrastructure.

> **Project status:** active research. Phase 0 API reconnaissance and Phase 1's explicit projective-line geometry are complete. Phase 2 is underway: the transition functions have been packaged, `O(n)` is constructed globally for every integer `n`, and its canonical local components and overlap gluing property are available through a public API. The next step is to prove its standard-chart restriction isomorphisms and identify `O(0)` with the structure sheaf. The Riemann-Roch theorem itself has not yet been formalized.

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
- the Phase 2 transition factors for `O(n)`, with the convention `e₁ = t^n e₀`, coefficient transport by `t^(-n)`, unit identities, and compatibility with the Laurent coordinate inversion;
- the global twisting sheaf `twistingSheaf k n` for every `n : ℤ`, constructed as the kernel of the compatibility map between the two pushed-forward trivial rank-one chart modules and the overlap module;
- canonical maps from `twistingSheaf k n` to both pushed-forward trivial chart modules, their overlap equation `a₁ = t^(-n) a₀`, and a universal gluing lift for compatible local data;
- design notes recording the relevant Mathlib APIs and the principal missing comparison theorems.

The next milestone is to prove that `twistingSheaf k n` restricts to the trivial rank-one module sheaf on each standard affine chart. The local-coordinate and gluing API now isolates that proof from the kernel implementation. Those local trivializations will support the identification `O(0) ≅ O`, the tensor and duality formulas, and the explicit Cech calculation.

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
| `RiemannRoch.ProjectiveLine.TwistingTransition` | Laurent frame and coefficient transition factors for the twisting sheaves `O(n)` |
| `RiemannRoch.ProjectiveLine.TwistingSheaf` | Global twisting sheaves as kernels of the two-chart overlap compatibility maps |
| `RiemannRoch.ProjectiveLine.TwistingSheafCoordinates` | Canonical chart components, overlap compatibility, and the universal gluing lift for `O(n)` |
| `RiemannRoch.ProjectiveLine.Target` | Integration boundary and projective-line theorem target |
| `RiemannRoch` | Main import file exporting the public development |
| [`BLUEPRINT.md`](BLUEPRINT.md) | Detailed phased roadmap and progress tracker |
| [`docs/`](docs/) | API inventories and design decisions, including the Phase 2 twisting-object construction |

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

Run `lake update` only when intentionally changing the pinned dependency metadata.

## Roadmap

1. Construct the twisting objects `O(n)` with explicit restriction data on the standard cover.
2. Calculate a normalized two-open Cech complex.
3. Prove `chi(P^1_k, O(n)) = n + 1`.
4. Extend the infrastructure to smooth projective curves.
5. Develop the K-theoretic and intersection-theoretic ingredients for Hirzebruch-Riemann-Roch and Grothendieck-Riemann-Roch.

The full dependency-aware roadmap is maintained in [`BLUEPRINT.md`](BLUEPRINT.md).

## Development standards

Every pull request is checked by GitHub Actions. CI builds the library, verifies that every module is exported by `RiemannRoch.lean`, and rejects unfinished `sorry` or `admit` placeholders.

Focused contributions, API suggestions, and mathematical corrections are welcome; see [`CONTRIBUTING.md`](CONTRIBUTING.md).

## References and acknowledgments

The project relies on [Mathlib](https://github.com/leanprover-community/mathlib4), particularly its implementations of graded rings, `Proj`, scheme-level basic opens, sheaves of modules, homogeneous localization, and sheaf cohomology.

The mathematical organization follows the standard route from the projective-line calculation to Riemann-Roch for curves and then toward its K-theoretic generalizations.

## Citation

Citation metadata is provided in [`CITATION.cff`](CITATION.cff). GitHub can also generate a formatted citation from the repository page.

## License

MIT License. See [`LICENSE`](LICENSE).
