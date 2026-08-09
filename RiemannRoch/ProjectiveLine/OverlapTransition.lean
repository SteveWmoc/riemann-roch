/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.Overlap

/-!
# Transition map on the standard overlap

This file compares the two Laurent-polynomial presentations of the standard
overlap of the projective line. The affine coordinates `X₁ / X₀` and
`X₀ / X₁` are reciprocal on the overlap, so the transition automorphism of
`k[t, t⁻¹]` is Laurent-polynomial inversion `t ↦ t⁻¹`.
-/

namespace RiemannRoch.ProjectiveLine

noncomputable section

universe u

/-- The two affine coordinates become mutual inverses on the standard overlap. -/
theorem overlapAffineCoordinates_mul_eq_one (k : Type u) [CommRing k] :
    x0ToOverlapMap k (x0AffineCoordinate k) *
      x1ToOverlapMap k (x1AffineCoordinate k) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [x0AffineCoordinate, x1AffineCoordinate, chartCoordinate,
    x0ToOverlapMap, x1ToOverlapMap, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_mul, ← Localization.mk_one,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp [overlapDenominator]
  ring

end

end RiemannRoch.ProjectiveLine
