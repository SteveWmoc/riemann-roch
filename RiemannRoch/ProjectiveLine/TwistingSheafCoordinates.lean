/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.TwistingSheaf

/-!
# Local coordinates for twisting sheaves on the projective line

This file packages the local-coordinate interface of the twisting sheaf `O(n)`.
The implementation of `twistingSheaf` is a kernel inside the category of module
sheaves on `P¹_k`; downstream arguments should instead use the two canonical
maps to the pushed-forward trivial chart modules and their overlap compatibility.

The main declarations are:

* `twistingSheafToX0` and `twistingSheafToX1`, the two local components;
* `twistingSheaf_overlap_condition`, expressing the coefficient relation
  `a₁ = t^(-n) a₀` on the overlap;
* `twistingSheafLift`, the corresponding universal gluing constructor;
* `twistingSheaf_hom_ext`, showing that the two local components determine a
  morphism into `O(n)`;
* `twistingSheafLift_unique`, the uniqueness half of the gluing universal
  property.

This API is intended to isolate later chart trivializations and Cech calculations
from the kernel used to construct `twistingSheaf`.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

universe u

/-- The `X0`-chart component of the twisting sheaf `O(n)`. -/
noncomputable abbrev twistingSheafToX0
    (k : Type u) [CommRing k] (n : ℤ) :
    twistingSheaf k n ⟶ x0PushedTrivialModule k :=
  twistingSheafι k n ≫ biprod.fst

/-- The `X1`-chart component of the twisting sheaf `O(n)`. -/
noncomputable abbrev twistingSheafToX1
    (k : Type u) [CommRing k] (n : ℤ) :
    twistingSheaf k n ⟶ x1PushedTrivialModule k :=
  twistingSheafι k n ≫ biprod.snd

/-- The two local components of `O(n)` obey the coefficient transition relation
`a₁ = t^(-n) a₀` after restriction to the standard overlap. -/
@[reassoc]
theorem twistingSheaf_overlap_condition
    (k : Type u) [CommRing k] (n : ℤ) :
    twistingSheafToX0 k n ≫ x0RestrictionToOverlap k ≫
        pushedOverlapCoefficientTransitionEnd k n =
      twistingSheafToX1 k n ≫ x1RestrictionToOverlap k := by
  have h := twistingSheafι_compatibility k n
  have hzero :
      twistingSheafToX0 k n ≫ x0RestrictionToOverlap k ≫
          pushedOverlapCoefficientTransitionEnd k n -
        twistingSheafToX1 k n ≫ x1RestrictionToOverlap k = 0 := by
    simpa [twistingSheafToX0, twistingSheafToX1, twistingCompatibilityMap,
      biprod.desc_eq, Preadditive.comp_add, Category.assoc, sub_eq_add_neg] using h
  exact sub_eq_zero.mp hzero

/-- Glue a compatible pair of maps to the two pushed-forward trivial chart
modules into a map to `O(n)`.

This is the kernel universal property expressed using the geometric local data:
compatibility means that the `X0` component, after coefficient transport by
`t^(-n)`, agrees with the `X1` component on the overlap. -/
noncomputable def twistingSheafLift
    (k : Type u) [CommRing k] (n : ℤ) {M : ModuleSheaf k}
    (f0 : M ⟶ x0PushedTrivialModule k)
    (f1 : M ⟶ x1PushedTrivialModule k)
    (h : f0 ≫ x0RestrictionToOverlap k ≫
          pushedOverlapCoefficientTransitionEnd k n =
        f1 ≫ x1RestrictionToOverlap k) :
    M ⟶ twistingSheaf k n :=
  kernel.lift (twistingCompatibilityMap k n) (biprod.lift f0 f1) (by
    simpa [twistingCompatibilityMap, sub_eq_add_neg, Category.assoc] using
      sub_eq_zero.mpr h)

@[reassoc (attr := simp)]
theorem twistingSheafLift_ι
    (k : Type u) [CommRing k] (n : ℤ) {M : ModuleSheaf k}
    (f0 : M ⟶ x0PushedTrivialModule k)
    (f1 : M ⟶ x1PushedTrivialModule k)
    (h : f0 ≫ x0RestrictionToOverlap k ≫
          pushedOverlapCoefficientTransitionEnd k n =
        f1 ≫ x1RestrictionToOverlap k) :
    twistingSheafLift k n f0 f1 h ≫ twistingSheafι k n =
      biprod.lift f0 f1 :=
  kernel.lift_ι _ _ _

@[reassoc (attr := simp)]
theorem twistingSheafLift_toX0
    (k : Type u) [CommRing k] (n : ℤ) {M : ModuleSheaf k}
    (f0 : M ⟶ x0PushedTrivialModule k)
    (f1 : M ⟶ x1PushedTrivialModule k)
    (h : f0 ≫ x0RestrictionToOverlap k ≫
          pushedOverlapCoefficientTransitionEnd k n =
        f1 ≫ x1RestrictionToOverlap k) :
    twistingSheafLift k n f0 f1 h ≫ twistingSheafToX0 k n = f0 := by
  simp [twistingSheafToX0]

@[reassoc (attr := simp)]
theorem twistingSheafLift_toX1
    (k : Type u) [CommRing k] (n : ℤ) {M : ModuleSheaf k}
    (f0 : M ⟶ x0PushedTrivialModule k)
    (f1 : M ⟶ x1PushedTrivialModule k)
    (h : f0 ≫ x0RestrictionToOverlap k ≫
          pushedOverlapCoefficientTransitionEnd k n =
        f1 ≫ x1RestrictionToOverlap k) :
    twistingSheafLift k n f0 f1 h ≫ twistingSheafToX1 k n = f1 := by
  simp [twistingSheafToX1]

/-- Morphisms into `O(n)` are determined by their two local components. -/
@[ext]
theorem twistingSheaf_hom_ext
    (k : Type u) [CommRing k] (n : ℤ) {M : ModuleSheaf k}
    {f g : M ⟶ twistingSheaf k n}
    (h0 : f ≫ twistingSheafToX0 k n = g ≫ twistingSheafToX0 k n)
    (h1 : f ≫ twistingSheafToX1 k n = g ≫ twistingSheafToX1 k n) :
    f = g := by
  apply Fork.IsLimit.hom_ext (kernelIsKernel (twistingCompatibilityMap k n))
  apply biprod.hom_ext
  · simpa [twistingSheafToX0, Category.assoc] using h0
  · simpa [twistingSheafToX1, Category.assoc] using h1

/-- The glued morphism is the unique morphism into `O(n)` with the prescribed
compatible local components. -/
theorem twistingSheafLift_unique
    (k : Type u) [CommRing k] (n : ℤ) {M : ModuleSheaf k}
    (f0 : M ⟶ x0PushedTrivialModule k)
    (f1 : M ⟶ x1PushedTrivialModule k)
    (h : f0 ≫ x0RestrictionToOverlap k ≫
          pushedOverlapCoefficientTransitionEnd k n =
        f1 ≫ x1RestrictionToOverlap k)
    (g : M ⟶ twistingSheaf k n)
    (h0 : g ≫ twistingSheafToX0 k n = f0)
    (h1 : g ≫ twistingSheafToX1 k n = f1) :
    g = twistingSheafLift k n f0 f1 h := by
  apply twistingSheaf_hom_ext k n
  · simpa using h0
  · simpa using h1

end

end RiemannRoch.ProjectiveLine
