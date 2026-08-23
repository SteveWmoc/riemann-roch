/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.HomologicalComplex
import RiemannRoch.ProjectiveLine.SheavesAndCech

/-!
# The normalized two-open Cech complex on the projective line

Mathlib's canonical Cech construction is unnormalized: in positive degree it
retains tuples with repeated cover indices. For the standard cover of `P¹_k` by
`D_+(X₀)` and `D_+(X₁)`, the explicit cohomology calculation is more naturally
expressed by the familiar two-term normalized complex

```text
Γ(D_+(X₀), M) ⊕ Γ(D_+(X₁), M)  -->  Γ(D_+(X₀) ∩ D_+(X₁), M),
                 (s₀, s₁)       |->  s₀| - s₁|.
```

This file packages that complex for an arbitrary module sheaf `M` on `P¹_k`.
It deliberately stays at the level of the underlying abelian presheaf. A later
comparison can relate this explicit complex to `standardCechComplex`, while the
twisting-sheaf calculation can transport it through the standard-chart
trivializations.
-/

namespace RiemannRoch.ProjectiveLine

open CategoryTheory Limits Opposite TopologicalSpace ZeroObject

noncomputable section

universe u

variable {k : Type u} [CommRing k]

/-- Degree zero of the normalized Cech complex for the standard two-open cover. -/
noncomputable abbrev standardNormalizedCechDegreeZero (M : ModuleSheaf k) :
    AddCommGrpCat :=
  M.presheaf.obj (op (x0BasicOpen k)) ⊞
    M.presheaf.obj (op (x1BasicOpen k))

/-- Degree one of the normalized Cech complex for the standard two-open cover. -/
noncomputable abbrev standardNormalizedCechDegreeOne (M : ModuleSheaf k) :
    AddCommGrpCat :=
  M.presheaf.obj (op (standardOverlap k))

/-- Restriction from the first standard chart to the overlap, on underlying
additive groups. -/
noncomputable abbrev standardNormalizedCechX0Restriction (M : ModuleSheaf k) :
    M.presheaf.obj (op (x0BasicOpen k)) ⟶
      M.presheaf.obj (op (standardOverlap k)) :=
  M.presheaf.map
    (homOfLE (show standardOverlap k ≤ x0BasicOpen k from inf_le_left)).op

/-- Restriction from the second standard chart to the overlap, on underlying
additive groups. -/
noncomputable abbrev standardNormalizedCechX1Restriction (M : ModuleSheaf k) :
    M.presheaf.obj (op (x1BasicOpen k)) ⟶
      M.presheaf.obj (op (standardOverlap k)) :=
  M.presheaf.map
    (homOfLE (show standardOverlap k ≤ x1BasicOpen k from inf_le_right)).op

/-- The normalized Cech differential `(s₀, s₁) ↦ s₀| - s₁|`. -/
noncomputable def standardNormalizedCechDifferential (M : ModuleSheaf k) :
    standardNormalizedCechDegreeZero M ⟶ standardNormalizedCechDegreeOne M :=
  biprod.desc
    (standardNormalizedCechX0Restriction M)
    (-standardNormalizedCechX1Restriction M)

@[reassoc (attr := simp)]
theorem standardNormalizedCech_inl_differential (M : ModuleSheaf k) :
    biprod.inl ≫ standardNormalizedCechDifferential M =
      standardNormalizedCechX0Restriction M := by
  simp [standardNormalizedCechDifferential]

@[reassoc (attr := simp)]
theorem standardNormalizedCech_inr_differential (M : ModuleSheaf k) :
    biprod.inr ≫ standardNormalizedCechDifferential M =
      -standardNormalizedCechX1Restriction M := by
  simp [standardNormalizedCechDifferential]

private noncomputable def standardNormalizedCechObjects (M : ModuleSheaf k) :
    ℕ → AddCommGrpCat
  | 0 => standardNormalizedCechDegreeZero M
  | Nat.succ 0 => standardNormalizedCechDegreeOne M
  | Nat.succ (Nat.succ _) => 0

private noncomputable def standardNormalizedCechD (M : ModuleSheaf k) :
    (i : ℕ) → standardNormalizedCechObjects M i ⟶
      standardNormalizedCechObjects M (i + 1)
  | 0 => standardNormalizedCechDifferential M
  | Nat.succ _ => 0

private theorem standardNormalizedCechD_squared (M : ModuleSheaf k) (i : ℕ) :
    standardNormalizedCechD M i ≫ standardNormalizedCechD M (i + 1) = 0 := by
  cases i <;> simp [standardNormalizedCechD]

/-- The normalized Cech complex for the standard cover of `P¹_k`. It is the
familiar two-term complex in degrees zero and one and is zero in all higher
degrees. -/
noncomputable def standardNormalizedCechComplex (M : ModuleSheaf k) :
    CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of
    (standardNormalizedCechObjects M)
    (standardNormalizedCechD M)
    (standardNormalizedCechD_squared M)

@[simp]
theorem standardNormalizedCechComplex_X_zero (M : ModuleSheaf k) :
    (standardNormalizedCechComplex M).X 0 =
      standardNormalizedCechDegreeZero M := by
  rfl

@[simp]
theorem standardNormalizedCechComplex_X_one (M : ModuleSheaf k) :
    (standardNormalizedCechComplex M).X 1 =
      standardNormalizedCechDegreeOne M := by
  rfl

@[simp]
theorem standardNormalizedCechComplex_X_add_two (M : ModuleSheaf k) (i : ℕ) :
    (standardNormalizedCechComplex M).X (i + 2) = 0 := by
  rfl

@[simp]
theorem standardNormalizedCechComplex_d_zero_one (M : ModuleSheaf k) :
    (standardNormalizedCechComplex M).d 0 1 =
      standardNormalizedCechDifferential M := by
  simp [standardNormalizedCechComplex, CochainComplex.of.d, standardNormalizedCechD]

end

end RiemannRoch.ProjectiveLine
