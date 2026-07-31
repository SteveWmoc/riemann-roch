/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The standard graded coordinate ring of the projective line

This file packages Mathlib's existing total-degree grading on the two-variable
multivariate polynomial ring. It intentionally introduces only thin aliases,
so downstream proofs can continue to use the underlying Mathlib API directly.
-/

namespace RiemannRoch.ProjectiveLine

noncomputable section

/-- The two homogeneous coordinate variables of the projective line. -/
abbrev Variable := Fin 2

/-- The homogeneous coordinate ring `k[X0, X1]`. -/
abbrev CoordinateRing (k : Type*) [CommRing k] := MvPolynomial Variable k

/-- The standard total-degree grading on `k[X0, X1]`. -/
abbrev grading (k : Type*) [CommRing k] : ℕ → Submodule k (CoordinateRing k) :=
  MvPolynomial.homogeneousSubmodule Variable k

/-- Mathlib's standard total-degree graded-algebra structure, installed for the
project-local name `grading`. -/
noncomputable instance gradingGradedAlgebra (k : Type*) [CommRing k] :
    GradedAlgebra (grading k) :=
  MvPolynomial.gradedAlgebra

/-- The first homogeneous coordinate. -/
abbrev x0 (k : Type*) [CommRing k] : CoordinateRing k :=
  MvPolynomial.X (0 : Variable)

/-- The second homogeneous coordinate. -/
abbrev x1 (k : Type*) [CommRing k] : CoordinateRing k :=
  MvPolynomial.X (1 : Variable)

/-- The first coordinate is homogeneous of degree one. -/
lemma x0_isHomogeneous (k : Type*) [CommRing k] :
    MvPolynomial.IsHomogeneous (x0 k) 1 :=
  MvPolynomial.isHomogeneous_X k (0 : Variable)

/-- The second coordinate is homogeneous of degree one. -/
lemma x1_isHomogeneous (k : Type*) [CommRing k] :
    MvPolynomial.IsHomogeneous (x1 k) 1 :=
  MvPolynomial.isHomogeneous_X k (1 : Variable)

/-- The first coordinate belongs to the degree-one component. -/
lemma x0_mem_grading_one (k : Type*) [CommRing k] : x0 k ∈ grading k 1 :=
  x0_isHomogeneous k

/-- The second coordinate belongs to the degree-one component. -/
lemma x1_mem_grading_one (k : Type*) [CommRing k] : x1 k ∈ grading k 1 :=
  x1_isHomogeneous k

end

end RiemannRoch.ProjectiveLine
