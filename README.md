# Riemann-Roch in Lean

[![CI](https://github.com/SteveWmoc/riemann-roch/actions/workflows/ci.yml/badge.svg)](https://github.com/SteveWmoc/riemann-roch/actions/workflows/ci.yml)

An experimental Lean 4 formalization of Riemann-Roch, beginning with the projective line and organized toward reusable algebraic-geometry infrastructure.

> **Project status:** active research. Phase 0 API reconnaissance is complete, and Phase 1 is developing explicit affine charts for the projective line. The Riemann-Roch theorem itself has not yet been formalized.

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
- the polynomial map `k[t] -> (k[X0, X1]_(X0))_0`, an explicit dehomogenization left inverse, and a proof that the map is injective;
- the category of sheaves of modules on `P^1_k` and the structure sheaf as a module;
- a specialization of Mathlib's canonical Cech-complex functor to the standard two-open cover;
- design notes recording the relevant Mathlib APIs and the principal missing comparison theorems.

The next algebraic milestone is to prove surjectivity of the polynomial map on the `X0` chart, package the resulting ring equivalence, and construct the corresponding equivalence on the `X1` chart. The overlap, twisting sheaves `O(n)`, the explicit normalized Cech calculation, and the comparison with derived sheaf cohomology remain future work.

## Repository layout

| Module or document | Contents |
| --- | --- |
| `RiemannRoch.ProjectiveLine.GradedPolynomialRing` | The coordinate ring `k[X0, X1]` and its standard grading |
| `RiemannRoch.ProjectiveLine.BasicOpens` | `P^1_k`, its standard homogeneous opens, and the cover theorem |
| `RiemannRoch.ProjectiveLine.AffineCharts` | Homogeneous-localization chart rings, open immersions, and ratio coordinates |
| `RiemannRoch.ProjectiveLine.Dehomogenization` | The `X0` polynomial chart map, dehomogenization, and injectivity theorem |
| `RiemannRoch.ProjectiveLine.SheavesAndCech` | Module sheaves and the canonical standard-cover Cech complex |
| `RiemannRoch.ProjectiveLine.Target` | Integration boundary and projective-line theorem target |
| `RiemannRoch` | Main import file exporting the public development |
| [`BLUEPRINT.md`](BLUEPRINT.md) | Detailed phased roadmap and progress tracker |
| [`docs/`](docs/) | Phase 0 API inventories and design decisions |

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

1. Complete the affine-coordinate descriptions of `P^1_k` and its standard overlap.
2. Construct the twisting sheaves `O(n)` with explicit restriction data.
3. Calculate a normalized two-open Cech complex.
4. Prove `chi(P^1_k, O(n)) = n + 1`.
5. Extend the infrastructure to smooth projective curves.
6. Develop the K-theoretic and intersection-theoretic ingredients for Hirzebruch-Riemann-Roch and Grothendieck-Riemann-Roch.

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
