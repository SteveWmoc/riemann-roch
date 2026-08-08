/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import Mathlib.Algebra.Polynomial.Laurent
import RiemannRoch.ProjectiveLine.AffineLineCharts

/-!
# The overlap of the standard affine charts

This file identifies the coordinate ring of the overlap of the two standard
charts of the projective line with the Laurent polynomial ring.

The key input is Mathlib's theorem that, for homogeneous `f` and `g`, the
homogeneous localization away from `f * g` is the localization of the `f`-chart
ring at the degree-zero ratio coordinate `g ^ deg(f) / f ^ deg(g)`. For
`f = X_0` and `g = X_1`, this ratio is exactly `X_1 / X_0`. Transporting along
the previously constructed equivalence `k[t] ≃+* standardAway k 0` therefore
identifies the overlap ring with `k[t, t⁻¹]`. The symmetric construction from
the `X_1` chart is also recorded in preparation for the transition map.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- The homogeneous element `X_0 X_1` cutting out the standard overlap. -/
abbrev overlapDenominator (k : Type u) [CommRing k] : CoordinateRing k :=
  coordinate k 0 * coordinate k 1

/-- The degree-zero homogeneous localization away from `X_0 X_1`. -/
abbrev overlapAway (k : Type u) [CommRing k] :=
  HomogeneousLocalization.Away (grading k) (overlapDenominator k)

/-- The standard overlap `D_+(X_0) ∩ D_+(X_1)`. -/
abbrev standardOverlap (k : Type u) [CommRing k] : (scheme k).Opens :=
  x0BasicOpen k ⊓ x1BasicOpen k

/-- The product `X_0 X_1` is homogeneous of degree two. -/
theorem overlapDenominator_mem_grading_two (k : Type u) [CommRing k] :
    overlapDenominator k ∈ grading k 2 := by
  simpa using SetLike.mul_mem_graded
    (coordinate_mem_grading_one k 0) (coordinate_mem_grading_one k 1)

/-- The homogeneous basic open of `X_0 X_1` is the intersection of the two
standard basic opens. -/
theorem basicOpen_overlapDenominator_eq_standardOverlap
    (k : Type u) [CommRing k] :
    AlgebraicGeometry.Proj.basicOpen (grading k) (overlapDenominator k) =
      standardOverlap k := by
  simpa using
    (AlgebraicGeometry.Proj.basicOpen_mul (grading k) (coordinate k 0) (coordinate k 1))

/-- The `X_0` chart map into the product localization. -/
noncomputable abbrev x0ToOverlapMap (k : Type u) [CommRing k] :
    standardAway k 0 →+* overlapAway k :=
  HomogeneousLocalization.awayMap (grading k)
    (coordinate_mem_grading_one k 1) rfl

/-- The overlap ring is the localization of the `X_0` chart ring at the affine
coordinate `X_1 / X_0`. -/
theorem overlapAway_isLocalization_x0AffineCoordinate
    (k : Type u) [CommRing k] :
    letI := (x0ToOverlapMap k).toAlgebra
    IsLocalization.Away (x0AffineCoordinate k) (overlapAway k) := by
  simpa [x0AffineCoordinate, chartCoordinate,
    HomogeneousLocalization.Away.isLocalizationElem] using
    (HomogeneousLocalization.Away.isLocalization_mul
      (𝒜 := grading k)
      (f := coordinate k 0) (g := coordinate k 1)
      (x := overlapDenominator k)
      (coordinate_mem_grading_one k 0)
      (coordinate_mem_grading_one k 1) rfl (by norm_num))

/-- The Laurent polynomial ring is isomorphic to the coordinate ring of the
standard overlap via the `X_0` chart. Under this equivalence, `T` corresponds
to `X_1 / X_0`. -/
noncomputable def laurentPolynomialEquivOverlapAway
    (k : Type u) [CommRing k] :
    LaurentPolynomial k ≃+* overlapAway k := by
  letI := (x0ToOverlapMap k).toAlgebra
  letI : IsLocalization.Away (x0AffineCoordinate k) (overlapAway k) :=
    overlapAway_isLocalization_x0AffineCoordinate k
  have hpow :
      (Submonoid.powers (Polynomial.X : Polynomial k)).map
          (x0ChartRingEquiv k).toMonoidHom =
        Submonoid.powers (x0AffineCoordinate k) := by
    ext y
    constructor
    · rintro ⟨z, ⟨n, rfl⟩, rfl⟩
      refine ⟨n, ?_⟩
      simp [x0ChartRingEquiv_apply]
    · rintro ⟨n, rfl⟩
      refine ⟨Polynomial.X ^ n, ⟨n, rfl⟩, ?_⟩
      simp [x0ChartRingEquiv_apply]
  exact IsLocalization.ringEquivOfRingEquiv
    (S := LaurentPolynomial k) (Q := overlapAway k)
    (M := Submonoid.powers (Polynomial.X : Polynomial k))
    (T := Submonoid.powers (x0AffineCoordinate k))
    (x0ChartRingEquiv k) hpow

/-- The `X_1` chart map into the product localization. -/
noncomputable abbrev x1ToOverlapMap (k : Type u) [CommRing k] :
    standardAway k 1 →+* overlapAway k :=
  HomogeneousLocalization.awayMap (grading k)
    (coordinate_mem_grading_one k 0)
    (mul_comm (coordinate k 0) (coordinate k 1))

/-- The overlap ring is the localization of the `X_1` chart ring at the affine
coordinate `X_0 / X_1`. -/
theorem overlapAway_isLocalization_x1AffineCoordinate
    (k : Type u) [CommRing k] :
    letI := (x1ToOverlapMap k).toAlgebra
    IsLocalization.Away (x1AffineCoordinate k) (overlapAway k) := by
  simpa [x1AffineCoordinate, chartCoordinate,
    HomogeneousLocalization.Away.isLocalizationElem] using
    (HomogeneousLocalization.Away.isLocalization_mul
      (𝒜 := grading k)
      (f := coordinate k 1) (g := coordinate k 0)
      (x := overlapDenominator k)
      (coordinate_mem_grading_one k 1)
      (coordinate_mem_grading_one k 0)
      (mul_comm (coordinate k 0) (coordinate k 1)) (by norm_num))

/-- The Laurent polynomial ring is isomorphic to the coordinate ring of the
standard overlap via the `X_1` chart. Under this equivalence, `T` corresponds
to `X_0 / X_1`. -/
noncomputable def laurentPolynomialEquivOverlapAwayX1
    (k : Type u) [CommRing k] :
    LaurentPolynomial k ≃+* overlapAway k := by
  letI := (x1ToOverlapMap k).toAlgebra
  letI : IsLocalization.Away (x1AffineCoordinate k) (overlapAway k) :=
    overlapAway_isLocalization_x1AffineCoordinate k
  have hpow :
      (Submonoid.powers (Polynomial.X : Polynomial k)).map
          (x1ChartRingEquiv k).toMonoidHom =
        Submonoid.powers (x1AffineCoordinate k) := by
    ext y
    constructor
    · rintro ⟨z, ⟨n, rfl⟩, rfl⟩
      refine ⟨n, ?_⟩
      simp [x1ChartRingEquiv_apply]
    · rintro ⟨n, rfl⟩
      refine ⟨Polynomial.X ^ n, ⟨n, rfl⟩, ?_⟩
      simp [x1ChartRingEquiv_apply]
  exact IsLocalization.ringEquivOfRingEquiv
    (S := LaurentPolynomial k) (Q := overlapAway k)
    (M := Submonoid.powers (Polynomial.X : Polynomial k))
    (T := Submonoid.powers (x1AffineCoordinate k))
    (x1ChartRingEquiv k) hpow

/-- The punctured affine line over `k`, represented by the Laurent polynomial
spectrum. -/
abbrev puncturedAffineLine (k : Type u) [CommRing k] : Scheme.{u} :=
  Spec (.of <| LaurentPolynomial k)

/-- The homogeneous basic open cut out by `X_0 X_1` has its canonical affine
presentation by the overlap ring. -/
noncomputable def overlapBasicOpenIsoSpec (k : Type u) [CommRing k] :
    (AlgebraicGeometry.Proj.basicOpen (grading k) (overlapDenominator k)).toScheme ≅
      Spec (.of <| overlapAway k) :=
  AlgebraicGeometry.Proj.basicOpenIsoSpec (grading k) (overlapDenominator k)
    (overlapDenominator_mem_grading_two k) (by norm_num)

/-- The literal intersection of the two standard opens is the spectrum of the
product homogeneous localization. -/
noncomputable def standardOverlapIsoSpec (k : Type u) [CommRing k] :
    (standardOverlap k).toScheme ≅ Spec (.of <| overlapAway k) :=
  (scheme k).isoOfEq (basicOpen_overlapDenominator_eq_standardOverlap k).symm ≪≫
    overlapBasicOpenIsoSpec k

/-- The spectrum of the overlap ring is the punctured affine line. -/
noncomputable def overlapSpecIsoPuncturedAffineLine (k : Type u) [CommRing k] :
    Spec (.of <| overlapAway k) ≅ puncturedAffineLine k :=
  Scheme.Spec.mapIso (laurentPolynomialEquivOverlapAway k).toCommRingCatIso.op

/-- The overlap `D_+(X_0) ∩ D_+(X_1)` is the punctured affine line
`Spec k[t, t⁻¹]`. -/
noncomputable def standardOverlapIsoPuncturedAffineLine
    (k : Type u) [CommRing k] :
    (standardOverlap k).toScheme ≅ puncturedAffineLine k :=
  standardOverlapIsoSpec k ≪≫ overlapSpecIsoPuncturedAffineLine k

end

end RiemannRoch.ProjectiveLine
