# Contributing

Contributions, questions, and mathematical corrections are welcome. This is an active research formalization, so the public API may evolve as the project moves from the projective line toward Riemann-Roch for curves and its generalizations.

## Development setup

The project uses Lean 4 and Mathlib through Lake. The exact versions are pinned by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

```sh
git clone https://github.com/SteveWmoc/riemann-roch.git
cd riemann-roch
lake build
```

Run `lake update` only when intentionally refreshing dependency metadata.

## Pull requests

Please keep pull requests focused on one mathematical or infrastructural goal. A good pull request should:

- explain the mathematical statement or repository improvement;
- describe the main proof idea when new mathematics is involved;
- state what is intentionally deferred;
- include documentation for public definitions and theorems;
- update `BLUEPRINT.md` and the README when a roadmap milestone changes;
- pass the repository CI checks.

Experimental work belongs on a feature branch. Code intended for Mathlib should be kept sufficiently general and documented to support later upstreaming.

## Lean style

- Follow Mathlib naming and formatting conventions where practical.
- Prefer small modules with explicit imports and a clear module docstring.
- Keep project-local aliases thin when the underlying Mathlib API is already suitable.
- Separate explicit coordinate calculations from general scheme-theoretic infrastructure.
- Avoid `sorry`, `admit`, and other unfinished proof placeholders.
- Keep helper declarations private unless they form part of a useful public API.
- Add a license header to every Lean source file.

## Documentation

The repository distinguishes three kinds of documentation:

- the README gives an outside reader the current mathematical scope;
- `BLUEPRINT.md` tracks milestones and dependencies;
- files under `docs/` record API inventories and design decisions.

Avoid duplicating long technical notes in several places. Link to the authoritative document instead.

## Licensing

By contributing, you agree that your contribution may be distributed under the MIT License used by this repository.
