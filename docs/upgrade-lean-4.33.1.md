# Lean 4.33.1 upgrade

This branch upgrades the project from Lean/Mathlib 4.32.1 to the latest stable 4.33.1 release pair.

The initial pin-only commit deliberately changes no mathematical source files. CI is used as the porting oracle; any source changes needed for Lean 4.33's transparency and Mathlib API changes will be kept in this upgrade PR.

The upgrade is especially desirable because Lean 4.32.2 fixed an additional kernel soundness bug after the project's previous 4.32.1 pin, while the 4.33 series contains further kernel and module-system hardening.
