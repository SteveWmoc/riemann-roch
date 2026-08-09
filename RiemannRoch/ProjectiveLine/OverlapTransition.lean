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
  letI : IsLocalization.Away (x0AffineCoordinate k) (overlapAway k) :=
    overlapAway_isLocalization_x0AffineCoordinate k
  change laurentPolynomialEquivOverlapAway k
      (algebraMap (Polynomial k) (LaurentPolynomial k) p) =
    algebraMap (standardAway k 0) (overlapAway k) (x0ChartRingEquiv k p)
  simp [laurentPolynomialEquivOverlapAway]
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent, IsLocalization.map_eq]
  rfl

/-- On ordinary polynomials, the `X₁` Laurent presentation is the chart-ring
map followed by localization to the overlap. -/
@[simp]
theorem laurentPolynomialEquivOverlapAwayX1_toLaurent
    (k : Type u) [CommRing k] (p : Polynomial k) :
    laurentPolynomialEquivOverlapAwayX1 k (Polynomial.toLaurent p) =
      x1ToOverlapMap k (x1ChartRingEquiv k p) := by
  letI := (x1ToOverlapMap k).toAlgebra
  letI : IsLocalization.Away (x1AffineCoordinate k) (overlapAway k) :=
    overlapAway_isLocalization_x1AffineCoordinate k
  change laurentPolynomialEquivOverlapAwayX1 k
      (algebraMap (Polynomial k) (LaurentPolynomial k) p) =
    algebraMap (standardAway k 1) (overlapAway k) (x1ChartRingEquiv k p)
  simp [laurentPolynomialEquivOverlapAwayX1]
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent, IsLocalization.map_eq]
  rfl

/-- The Laurent generator in the `X₀` presentation maps to `X₁ / X₀`. -/
@[simp]
theorem laurentPolynomialEquivOverlapAway_T_one
    (k : Type u) [CommRing k] :
    laurentPolynomialEquivOverlapAway k (LaurentPolynomial.T 1) =
      x0ToOverlapMap k (x0AffineCoordinate k) := by
  simpa using laurentPolynomialEquivOverlapAway_toLaurent k Polynomial.X

/-- The Laurent generator in the `X₁` presentation maps to `X₀ / X₁`. -/
@[simp]
theorem laurentPolynomialEquivOverlapAwayX1_T_one
    (k : Type u) [CommRing k] :
    laurentPolynomialEquivOverlapAwayX1 k (LaurentPolynomial.T 1) =
      x1ToOverlapMap k (x1AffineCoordinate k) := by
  simpa using laurentPolynomialEquivOverlapAwayX1_toLaurent k Polynomial.X

/-- The two Laurent presentations agree on coefficients. -/
theorem laurentPolynomialEquivOverlapAway_C_eq_X1_C
    (k : Type u) [CommRing k] (r : k) :
    laurentPolynomialEquivOverlapAway k (LaurentPolynomial.C r) =
      laurentPolynomialEquivOverlapAwayX1 k (LaurentPolynomial.C r) := by
  calc
    laurentPolynomialEquivOverlapAway k (LaurentPolynomial.C r) =
        x0ToOverlapMap k (x0ChartRingEquiv k (Polynomial.C r)) := by
      simpa using laurentPolynomialEquivOverlapAway_toLaurent k (Polynomial.C r)
    _ = x1ToOverlapMap k (x1ChartRingEquiv k (Polynomial.C r)) := by
      simp [x0ChartRingEquiv_apply, x1ChartRingEquiv_apply,
        coefficientToStandardAway, x0ToOverlapMap, x1ToOverlapMap,
        HomogeneousLocalization.awayMap_fromZeroRingHom]
    _ = laurentPolynomialEquivOverlapAwayX1 k (LaurentPolynomial.C r) := by
      simpa using (laurentPolynomialEquivOverlapAwayX1_toLaurent k (Polynomial.C r)).symm

/-- The `X₀` Laurent generator is the inverse Laurent generator in the `X₁`
presentation. -/
theorem laurentPolynomialEquivOverlapAway_T_one_eq_X1_T_neg_one
    (k : Type u) [CommRing k] :
    laurentPolynomialEquivOverlapAway k (LaurentPolynomial.T 1) =
      laurentPolynomialEquivOverlapAwayX1 k (LaurentPolynomial.T (-1)) := by
  have hcoord :
      laurentPolynomialEquivOverlapAway k (LaurentPolynomial.T 1) *
        laurentPolynomialEquivOverlapAwayX1 k (LaurentPolynomial.T 1) = 1 := by
    simpa using overlapAffineCoordinates_mul_eq_one k
  have hinv :
      laurentPolynomialEquivOverlapAwayX1 k (LaurentPolynomial.T (-1)) *
        laurentPolynomialEquivOverlapAwayX1 k (LaurentPolynomial.T 1) = 1 := by
    rw [← map_mul, ← LaurentPolynomial.T_add]
    norm_num
  calc
    laurentPolynomialEquivOverlapAway k (LaurentPolynomial.T 1) =
        laurentPolynomialEquivOverlapAway k (LaurentPolynomial.T 1) * 1 :=
      (mul_one _).symm
    _ = laurentPolynomialEquivOverlapAway k (LaurentPolynomial.T 1) *
        (laurentPolynomialEquivOverlapAwayX1 k (LaurentPolynomial.T (-1)) *
          laurentPolynomialEquivOverlapAwayX1 k (LaurentPolynomial.T 1)) := by
      rw [hinv]
    _ = (laurentPolynomialEquivOverlapAway k (LaurentPolynomial.T 1) *
        laurentPolynomialEquivOverlapAwayX1 k (LaurentPolynomial.T 1)) *
          laurentPolynomialEquivOverlapAwayX1 k (LaurentPolynomial.T (-1)) := by
      ring
    _ = laurentPolynomialEquivOverlapAwayX1 k (LaurentPolynomial.T (-1)) := by
      rw [hcoord, one_mul]

/-- The `X₀` Laurent presentation is the `X₁` Laurent presentation after
substituting `T ↦ T⁻¹`. -/
theorem laurentPolynomialEquivOverlapAway_eq_X1_comp_invert
    (k : Type u) [CommRing k] :
    (laurentPolynomialEquivOverlapAway k).toRingHom =
      (laurentPolynomialEquivOverlapAwayX1 k).toRingHom.comp
        (LaurentPolynomial.invert (R := k)).toRingEquiv.toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial k))
  apply Polynomial.ringHom_ext
  · intro r
    simpa using laurentPolynomialEquivOverlapAway_C_eq_X1_C k r
  · simpa using laurentPolynomialEquivOverlapAway_T_one_eq_X1_T_neg_one k

/-- Change Laurent coordinates on the overlap from the `X₀` chart coordinate
`X₁ / X₀` to the `X₁` chart coordinate `X₀ / X₁`. -/
noncomputable def overlapLaurentTransition (k : Type u) [CommRing k] :
    LaurentPolynomial k ≃+* LaurentPolynomial k :=
  (laurentPolynomialEquivOverlapAway k).trans
    (laurentPolynomialEquivOverlapAwayX1 k).symm

/-- The standard overlap transition is Laurent-polynomial inversion
`T ↦ T⁻¹`. -/
theorem overlapLaurentTransition_eq_invert (k : Type u) [CommRing k] :
    overlapLaurentTransition k =
      (LaurentPolynomial.invert (R := k)).toRingEquiv := by
  apply RingEquiv.ext
  intro f
  apply (laurentPolynomialEquivOverlapAwayX1 k).injective
  have hf := RingHom.congr_fun
    (laurentPolynomialEquivOverlapAway_eq_X1_comp_invert k) f
  simpa [overlapLaurentTransition] using hf

/-- On Laurent monomials, the overlap transition negates the exponent. -/
@[simp]
theorem overlapLaurentTransition_T (k : Type u) [CommRing k] (n : ℤ) :
    overlapLaurentTransition k (LaurentPolynomial.T n) =
      LaurentPolynomial.T (-n) := by
  rw [overlapLaurentTransition_eq_invert]
  simp

end

end RiemannRoch.ProjectiveLine
