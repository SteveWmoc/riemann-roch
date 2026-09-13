# Lean 4.33.1 upgrade

The project was upgraded from the Lean/Mathlib 4.32.1 release pair to 4.33.1.
The current versions are pinned by `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`.

The migration initially used CI as the porting oracle and required source-level
adjustments for Lean 4.33 transparency behavior and Mathlib API changes. The
upgrade is complete; this note is retained as a historical marker rather than a
plan for an active branch.

The upgrade was especially desirable because Lean 4.32.2 fixed an additional
kernel soundness bug after the project's previous 4.32.1 pin, while the 4.33
series contains further kernel and module-system hardening.
