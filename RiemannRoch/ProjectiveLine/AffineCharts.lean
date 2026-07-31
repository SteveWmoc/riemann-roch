/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import RiemannRoch.ProjectiveLine.BasicOpens

/-!
# Canonical affine presentations of the standard charts

Mathlib identifies a positive-degree homogeneous basic open of `Proj` with the
spectrum of the degree-zero part of the corresponding homogeneous localization.
This file packages that construction for the two standard charts of `P^1_k`.

The remaining algebraic step toward the familiar affine-line charts is to prove
that each `standardAway k i` is isomorphic to a one-variable polynomial ring.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- The degree-zero homogeneous localization of `k[X0, X1]` away from `X_i`. -/
abbrev standardAway (k : Type u) [CommRing k] (i : Variable) :=
  HomogeneousLocalization.Away (grading k) (coordinate k i)

/-- The canonical affine presentation
`D_+(X_i) ≅ Spec ((k[X0, X1]_{X_i})_0)`. -/
noncomputable def standardBasicOpenIsoSpec (k : Type u) [CommRing k] (i : Variable) :
    (standardBasicOpen k i).toScheme ≅ Spec (.of <| standardAway k i) :=
  AlgebraicGeometry.Proj.basicOpenIsoSpec (grading k) (coordinate k i)
    (coordinate_mem_grading_one k i) (by positivity)

/-- The canonical affine presentation of `D_+(X_0)`. -/
noncomputable def x0BasicOpenIsoSpec (k : Type u) [CommRing k] :
    (x0BasicOpen k).toScheme ≅ Spec (.of <| standardAway k 0) :=
  standardBasicOpenIsoSpec k 0

/-- The canonical affine presentation of `D_+(X_1)`. -/
noncomputable def x1BasicOpenIsoSpec (k : Type u) [CommRing k] :
    (x1BasicOpen k).toScheme ≅ Spec (.of <| standardAway k 1) :=
  standardBasicOpenIsoSpec k 1

/-- The open immersion from the affine presentation of the `i`th standard chart
back into the projective line. -/
noncomputable def standardAwayOpenImmersion (k : Type u) [CommRing k] (i : Variable) :
    Spec (.of <| standardAway k i) ⟶ scheme k :=
  AlgebraicGeometry.Proj.awayι (grading k) (coordinate k i)
    (coordinate_mem_grading_one k i) (by positivity)

/-- The canonical chart map is an open immersion. -/
instance (k : Type u) [CommRing k] (i : Variable) :
    IsOpenImmersion (standardAwayOpenImmersion k i) := by
  dsimp [standardAwayOpenImmersion]
  infer_instance

/-- The open immersion from the affine presentation has image exactly `D_+(X_i)`. -/
theorem opensRange_standardAwayOpenImmersion (k : Type u) [CommRing k] (i : Variable) :
    (standardAwayOpenImmersion k i).opensRange = standardBasicOpen k i := by
  exact AlgebraicGeometry.Proj.opensRange_awayι (grading k) (coordinate k i)
    (coordinate_mem_grading_one k i) (by positivity)

/-- Each standard homogeneous basic open is affine. -/
theorem standardBasicOpen_isAffine (k : Type u) [CommRing k] (i : Variable) :
    IsAffineOpen (standardBasicOpen k i) := by
  exact AlgebraicGeometry.Proj.isAffineOpen_basicOpen (grading k) (coordinate k i)
    (coordinate_mem_grading_one k i) (by positivity)

/-- The degree-zero fraction `X_j / X_i` in the `i`th chart ring. -/
noncomputable def chartCoordinate (k : Type u) [CommRing k] (i j : Variable) :
    standardAway k i :=
  HomogeneousLocalization.Away.mk (grading k) (coordinate_mem_grading_one k i) 1
    (coordinate k j) (by simpa using coordinate_mem_grading_one k j)

/-- The usual affine coordinate `X_1 / X_0` on `D_+(X_0)`. -/
noncomputable def x0AffineCoordinate (k : Type u) [CommRing k] : standardAway k 0 :=
  chartCoordinate k 0 1

/-- The usual affine coordinate `X_0 / X_1` on `D_+(X_1)`. -/
noncomputable def x1AffineCoordinate (k : Type u) [CommRing k] : standardAway k 1 :=
  chartCoordinate k 1 0

/-- Evaluation at `X_j / X_i`, initially viewed as an algebra map over the
degree-zero component of the homogeneous coordinate ring. -/
noncomputable def chartPolynomialMap (k : Type u) [CommRing k] (i j : Variable) :
    Polynomial (grading k 0) →ₐ[grading k 0] standardAway k i :=
  Polynomial.aeval (chartCoordinate k i j)

/-- Evaluation sends the polynomial variable to the corresponding ratio coordinate. -/
@[simp]
theorem chartPolynomialMap_X (k : Type u) [CommRing k] (i j : Variable) :
    chartPolynomialMap k i j Polynomial.X = chartCoordinate k i j := by
  simp [chartPolynomialMap]

end

end RiemannRoch.ProjectiveLine
