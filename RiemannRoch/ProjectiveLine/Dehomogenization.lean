/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.RingTheory.Localization.Away.Basic
import RiemannRoch.ProjectiveLine.AffineCharts

/-!
# Dehomogenization on the first standard chart

This file begins the explicit identification of the standard chart `D_+(X_0)`
with the affine line. It defines the polynomial map

```text
k[t] -> (k[X_0, X_1]_(X_0))_0,   t |-> X_1 / X_0,
```

together with a dehomogenization map in the reverse direction obtained by
setting `X_0 = 1` and `X_1 = t`. The first milestone is to prove that
dehomogenization is a left inverse, hence that the polynomial map is injective.

Surjectivity, and therefore the full ring equivalence, is intentionally deferred
to the next step.
-/

namespace RiemannRoch.ProjectiveLine

noncomputable section

universe u

/-- Embed coefficients into the degree-zero part of the homogeneous coordinate
ring. -/
noncomputable def degreeZeroCoefficientMap (k : Type u) [CommRing k] :
    k →+* grading k 0 where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ r⟩
  map_one' := by ext; simp
  map_mul' r s := by ext; simp
  map_zero' := by ext; simp
  map_add' r s := by ext; simp

/-- Embed coefficients into the `i`th homogeneous-localization chart ring. -/
noncomputable def coefficientToStandardAway (k : Type u) [CommRing k] (i : Variable) :
    k →+* standardAway k i :=
  (HomogeneousLocalization.fromZeroRingHom
      (grading k) (Submonoid.powers (coordinate k i))).comp
    (degreeZeroCoefficientMap k)

/-- The polynomial map `k[t] -> (k[X_0, X_1]_(X_0))_0` sending `t` to
`X_1 / X_0`. -/
noncomputable def x0PolynomialMap (k : Type u) [CommRing k] :
    Polynomial k →+* standardAway k 0 :=
  Polynomial.eval₂RingHom (coefficientToStandardAway k 0) (x0AffineCoordinate k)

@[simp]
theorem x0PolynomialMap_C (k : Type u) [CommRing k] (r : k) :
    x0PolynomialMap k (Polynomial.C r) = coefficientToStandardAway k 0 r := by
  simp [x0PolynomialMap]

@[simp]
theorem x0PolynomialMap_X (k : Type u) [CommRing k] :
    x0PolynomialMap k Polynomial.X = x0AffineCoordinate k := by
  simp [x0PolynomialMap]

/-- Dehomogenize a bivariate polynomial by setting `X_0 = 1` and
`X_1 = t`. -/
noncomputable def x0CoordinateRingDehomogenizeHom (k : Type u) [CommRing k] :
    CoordinateRing k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C ![1, Polynomial.X]

@[simp]
theorem x0CoordinateRingDehomogenizeHom_x0 (k : Type u) [CommRing k] :
    x0CoordinateRingDehomogenizeHom k (coordinate k 0) = 1 := by
  simp [x0CoordinateRingDehomogenizeHom, coordinate]

@[simp]
theorem x0CoordinateRingDehomogenizeHom_x1 (k : Type u) [CommRing k] :
    x0CoordinateRingDehomogenizeHom k (coordinate k 1) = Polynomial.X := by
  simp [x0CoordinateRingDehomogenizeHom, coordinate]

/-- Extend dehomogenization to the ordinary localization away from `X_0`. -/
noncomputable def x0LocalizationDehomogenizeHom (k : Type u) [CommRing k] :
    Localization.Away (coordinate k 0) →+* Polynomial k :=
  Localization.awayLift (x0CoordinateRingDehomogenizeHom k) (coordinate k 0) (by
    simp)

/-- Restrict dehomogenization to the degree-zero homogeneous localization. -/
noncomputable def x0DehomogenizeHom (k : Type u) [CommRing k] :
    standardAway k 0 →+* Polynomial k :=
  (x0LocalizationDehomogenizeHom k).comp
    (algebraMap (standardAway k 0) (Localization.Away (coordinate k 0)))

@[simp]
theorem x0DehomogenizeHom_affineCoordinate (k : Type u) [CommRing k] :
    x0DehomogenizeHom k (x0AffineCoordinate k) = Polynomial.X := by
  let g := x0CoordinateRingDehomogenizeHom k
  have hg : g (coordinate k 0) * (1 : Polynomial k) = 1 := by
    simp [g]
  have h := Localization.awayLift_mk g (coordinate k 0) (coordinate k 1)
    (1 : Polynomial k) hg 1
  simpa [x0DehomogenizeHom, x0LocalizationDehomogenizeHom, x0AffineCoordinate,
    chartCoordinate, g, x0CoordinateRingDehomogenizeHom, coordinate] using h

@[simp]
theorem x0DehomogenizeHom_coefficient (k : Type u) [CommRing k] (r : k) :
    x0DehomogenizeHom k (coefficientToStandardAway k 0 r) = Polynomial.C r := by
  let g := x0CoordinateRingDehomogenizeHom k
  have hg : g (coordinate k 0) * (1 : Polynomial k) = 1 := by
    simp [g]
  have h := Localization.awayLift_mk g (coordinate k 0) (MvPolynomial.C r)
    (1 : Polynomial k) hg 0
  simpa [x0DehomogenizeHom, x0LocalizationDehomogenizeHom,
    coefficientToStandardAway, degreeZeroCoefficientMap,
    HomogeneousLocalization.fromZeroRingHom, g,
    x0CoordinateRingDehomogenizeHom, coordinate] using h

/-- Dehomogenization is a left inverse to the polynomial chart map. -/
theorem x0DehomogenizeHom_leftInverse (k : Type u) [CommRing k] :
    Function.LeftInverse (x0DehomogenizeHom k) (x0PolynomialMap k) := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n r =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp

/-- The polynomial map into the first standard chart ring is injective. -/
theorem x0PolynomialMap_injective (k : Type u) [CommRing k] :
    Function.Injective (x0PolynomialMap k) :=
  (x0DehomogenizeHom_leftInverse k).injective

end

end RiemannRoch.ProjectiveLine
