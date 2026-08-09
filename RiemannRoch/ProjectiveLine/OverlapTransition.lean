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

/-- On ordinary polynomials, the `X₀` Laurent presentation is the chart-ring
map followed by localization to the overlap. -/
@[simp]
theorem laurentPolynomialEquivOverlapAway_toLaurent
    (k : Type u) [CommRing k] (p : Polynomial k) :
    laurentPolynomialEquivOverlapAway k (Polynomial.toLaurent p) =
      x0ToOverlapMap k (x0ChartRingEquiv k p) := by
  letI := (x0ToOverlapMap k).toAlgebra
  change laurentPolynomialEquivOverlapAway k
      (algebraMap (Polynomial k) (LaurentPolynomial k) p) =
    algebraMap (standardAway k 0) (overlapAway k) (x0ChartRingEquiv k p)
  simp [laurentPolynomialEquivOverlapAway]

/-- On ordinary polynomials, the `X₁` Laurent presentation is the chart-ring
map followed by localization to the overlap. -/
@[simp]
theorem laurentPolynomialEquivOverlapAwayX1_toLaurent
    (k : Type u) [CommRing k] (p : Polynomial k) :
    laurentPolynomialEquivOverlapAwayX1 k (Polynomial.toLaurent p) =
      x1ToOverlapMap k (x1ChartRingEquiv k p) := by
  letI := (x1ToOverlapMap k).toAlgebra
  change laurentPolynomialEquivOverlapAwayX1 k
      (algebraMap (Polynomial k) (LaurentPolynomial k) p) =
    algebraMap (standardAway k 1) (overlapAway k) (x1ChartRingEquiv k p)
  simp [laurentPolynomialEquivOverlapAwayX1]

end

end RiemannRoch.ProjectiveLine
