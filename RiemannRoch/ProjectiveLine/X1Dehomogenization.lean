/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.Dehomogenization

/-!
# Dehomogenization on the second standard chart

This file identifies the degree-zero homogeneous localization on the second
standard chart with a one-variable polynomial ring. It defines the polynomial
map

```text
k[t] -> (k[X_0, X_1]_(X_1))_0,   t |-> X_0 / X_1,
```

and the reverse dehomogenization map obtained by setting `X_0 = t` and
`X_1 = 1`. Mathlib's native polynomial homogenization uses `X_1` as the
homogenizing variable, so homogeneous numerators are reconstructed directly.
The two maps are therefore inverse ring equivalences.
-/

namespace RiemannRoch.ProjectiveLine

noncomputable section

universe u

/-- Homogenize a polynomial using `X_1` as the homogenizing variable and `X_0`
as the affine variable. -/
noncomputable def x1Homogenize (k : Type u) [CommRing k]
    (p : Polynomial k) (n : ℕ) : CoordinateRing k :=
  Polynomial.homogenize p n

/-- The `X_1`-homogenization of a polynomial is homogeneous of the requested degree. -/
theorem x1Homogenize_mem_grading (k : Type u) [CommRing k]
    (p : Polynomial k) (n : ℕ) :
    x1Homogenize k p n ∈ grading k n := by
  exact Polynomial.isHomogeneous_homogenize p

@[simp]
theorem x1Homogenize_zero (k : Type u) [CommRing k] (n : ℕ) :
    x1Homogenize k 0 n = 0 := by
  simp [x1Homogenize]

/-- The polynomial map `k[t] -> (k[X_0, X_1]_(X_1))_0` sending `t` to
`X_0 / X_1`. -/
noncomputable def x1PolynomialMap (k : Type u) [CommRing k] :
    Polynomial k →+* standardAway k 1 :=
  Polynomial.eval₂RingHom (coefficientToStandardAway k 1) (x1AffineCoordinate k)

@[simp]
theorem x1PolynomialMap_C (k : Type u) [CommRing k] (r : k) :
    x1PolynomialMap k (Polynomial.C r) = coefficientToStandardAway k 1 r := by
  simp [x1PolynomialMap]

@[simp]
theorem x1PolynomialMap_X (k : Type u) [CommRing k] :
    x1PolynomialMap k Polynomial.X = x1AffineCoordinate k := by
  simp [x1PolynomialMap]

/-- Dehomogenize a bivariate polynomial by setting `X_0 = t` and
`X_1 = 1`. -/
noncomputable def x1CoordinateRingDehomogenizeHom (k : Type u) [CommRing k] :
    CoordinateRing k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1]

@[simp]
theorem x1CoordinateRingDehomogenizeHom_x0 (k : Type u) [CommRing k] :
    x1CoordinateRingDehomogenizeHom k (coordinate k 0) = Polynomial.X := by
  simp [x1CoordinateRingDehomogenizeHom, coordinate]

@[simp]
theorem x1CoordinateRingDehomogenizeHom_x1 (k : Type u) [CommRing k] :
    x1CoordinateRingDehomogenizeHom k (coordinate k 1) = 1 := by
  simp [x1CoordinateRingDehomogenizeHom, coordinate]

/-- A homogeneous bivariate polynomial is recovered by dehomogenizing at
`X_1 = 1` and then homogenizing again with `X_1`. -/
theorem x1Homogenize_dehomogenize_of_isHomogeneous
    (k : Type u) [CommRing k] (p : CoordinateRing k) (n : ℕ)
    (hp : p ∈ grading k n) :
    x1Homogenize k (x1CoordinateRingDehomogenizeHom k p) n = p := by
  exact Polynomial.homogenize_eq_of_isHomogeneous hp rfl

/-- Extend dehomogenization to the ordinary localization away from `X_1`. -/
noncomputable def x1LocalizationDehomogenizeHom (k : Type u) [CommRing k] :
    Localization.Away (coordinate k 1) →+* Polynomial k :=
  Localization.awayLift (x1CoordinateRingDehomogenizeHom k) (coordinate k 1) (by
    simp)

/-- Restrict dehomogenization to the degree-zero homogeneous localization. -/
noncomputable def x1DehomogenizeHom (k : Type u) [CommRing k] :
    standardAway k 1 →+* Polynomial k :=
  (x1LocalizationDehomogenizeHom k).comp
    (algebraMap (standardAway k 1) (Localization.Away (coordinate k 1)))

@[simp]
theorem x1DehomogenizeHom_awayMk (k : Type u) [CommRing k]
    (n : ℕ) (p : CoordinateRing k) (hp : p ∈ grading k n) :
    x1DehomogenizeHom k
        (HomogeneousLocalization.Away.mk (grading k)
          (coordinate_mem_grading_one k 1) n p (by simpa using hp)) =
      x1CoordinateRingDehomogenizeHom k p := by
  let g := x1CoordinateRingDehomogenizeHom k
  have hg : g (coordinate k 1) * (1 : Polynomial k) = 1 := by
    simp [g]
  have h := Localization.awayLift_mk g (coordinate k 1) p
    (1 : Polynomial k) hg n
  simpa [x1DehomogenizeHom, x1LocalizationDehomogenizeHom,
    HomogeneousLocalization.algebraMap_apply, g] using h

@[simp]
theorem x1DehomogenizeHom_affineCoordinate (k : Type u) [CommRing k] :
    x1DehomogenizeHom k (x1AffineCoordinate k) = Polynomial.X := by
  let g := x1CoordinateRingDehomogenizeHom k
  have hg : g (coordinate k 1) * (1 : Polynomial k) = 1 := by
    simp [g]
  have h := Localization.awayLift_mk g (coordinate k 1) (coordinate k 0)
    (1 : Polynomial k) hg 1
  simpa [x1DehomogenizeHom, x1LocalizationDehomogenizeHom, x1AffineCoordinate,
    chartCoordinate, g, x1CoordinateRingDehomogenizeHom, coordinate] using h

@[simp]
theorem x1DehomogenizeHom_coefficient (k : Type u) [CommRing k] (r : k) :
    x1DehomogenizeHom k (coefficientToStandardAway k 1 r) = Polynomial.C r := by
  let g := x1CoordinateRingDehomogenizeHom k
  have hg : g (coordinate k 1) * (1 : Polynomial k) = 1 := by
    simp [g]
  have h := Localization.awayLift_mk g (coordinate k 1) (MvPolynomial.C r)
    (1 : Polynomial k) hg 0
  simpa [x1DehomogenizeHom, x1LocalizationDehomogenizeHom,
    coefficientToStandardAway, degreeZeroCoefficientMap,
    HomogeneousLocalization.fromZeroRingHom, g,
    x1CoordinateRingDehomogenizeHom, coordinate] using h

/-- Dehomogenization is a left inverse to the polynomial chart map. -/
theorem x1DehomogenizeHom_leftInverse (k : Type u) [CommRing k] :
    Function.LeftInverse (x1DehomogenizeHom k) (x1PolynomialMap k) := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n r =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp

/-- The polynomial map into the second standard chart ring is injective. -/
theorem x1PolynomialMap_injective (k : Type u) [CommRing k] :
    Function.Injective (x1PolynomialMap k) :=
  (x1DehomogenizeHom_leftInverse k).injective

/-- An element of the second chart ring dehomogenizes to zero exactly when it is zero. -/
theorem x1DehomogenizeHom_eq_zero_iff (k : Type u) [CommRing k]
    (z : standardAway k 1) :
    x1DehomogenizeHom k z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    obtain ⟨n, p, hp, hrep⟩ :=
      HomogeneousLocalization.Away.mk_surjective (grading k)
        (coordinate_mem_grading_one k 1) z
    have hp' : p ∈ grading k n := by
      simpa using hp
    have hdp : x1CoordinateRingDehomogenizeHom k p = 0 := by
      rw [← x1DehomogenizeHom_awayMk k n p hp', hrep]
      exact hz
    have hpzero : p = 0 := by
      rw [← x1Homogenize_dehomogenize_of_isHomogeneous k p n hp']
      simp [hdp]
    rw [← hrep]
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk, hpzero, Localization.mk_zero,
      HomogeneousLocalization.val_zero]
  · rintro rfl
    simp

/-- Dehomogenization on the second chart ring is injective. -/
theorem x1DehomogenizeHom_injective (k : Type u) [CommRing k] :
    Function.Injective (x1DehomogenizeHom k) := by
  intro z w h
  apply sub_eq_zero.mp
  apply (x1DehomogenizeHom_eq_zero_iff k (z - w)).mp
  rw [map_sub, h, sub_self]

/-- Dehomogenization is also a right inverse to the polynomial chart map. -/
theorem x1DehomogenizeHom_rightInverse (k : Type u) [CommRing k] :
    Function.RightInverse (x1DehomogenizeHom k) (x1PolynomialMap k) := by
  intro z
  apply x1DehomogenizeHom_injective k
  exact x1DehomogenizeHom_leftInverse k (x1DehomogenizeHom k z)

/-- The polynomial map into the second standard chart ring is surjective. -/
theorem x1PolynomialMap_surjective (k : Type u) [CommRing k] :
    Function.Surjective (x1PolynomialMap k) :=
  (x1DehomogenizeHom_rightInverse k).surjective

/-- The second standard chart ring is the one-variable polynomial ring. -/
noncomputable def x1ChartRingEquiv (k : Type u) [CommRing k] :
    Polynomial k ≃+* standardAway k 1 :=
  RingEquiv.ofBijective (x1PolynomialMap k)
    ⟨x1PolynomialMap_injective k, x1PolynomialMap_surjective k⟩

@[simp]
theorem x1ChartRingEquiv_apply (k : Type u) [CommRing k] (p : Polynomial k) :
    x1ChartRingEquiv k p = x1PolynomialMap k p :=
  rfl

@[simp]
theorem x1ChartRingEquiv_symm_apply (k : Type u) [CommRing k]
    (z : standardAway k 1) :
    (x1ChartRingEquiv k).symm z = x1DehomogenizeHom k z := by
  apply x1PolynomialMap_injective k
  calc
    x1PolynomialMap k ((x1ChartRingEquiv k).symm z) = z := by
      change x1ChartRingEquiv k ((x1ChartRingEquiv k).symm z) = z
      exact (x1ChartRingEquiv k).apply_symm_apply z
    _ = x1PolynomialMap k (x1DehomogenizeHom k z) :=
      (x1DehomogenizeHom_rightInverse k z).symm

end

end RiemannRoch.ProjectiveLine
