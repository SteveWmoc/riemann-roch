/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import Mathlib.Topology.Sheaves.Stalks
import RiemannRoch.ProjectiveLine.TwistingSheafX1Trivialization

/-!
# The untwisted twisting sheaf

This file identifies the twisting sheaf `O(0)` with the structure sheaf of
`P¹_k`.

The comparison morphism is obtained by restricting a structure-sheaf section
to the two standard charts and applying the local-coordinate gluing universal
property of `twistingSheaf`. It is an isomorphism because its restriction to
each member of the standard cover is an isomorphism.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

/-- The structure sheaf, regarded as its own rank-one module sheaf. -/
noncomputable abbrev structureModule (k : Type u) [CommRing k] : ModuleSheaf k :=
  SheafOfModules.unit (scheme k).ringCatSheaf

/-- The constant unit section of the first pushed-forward trivial chart
module. -/
noncomputable def x0PushedTrivialUnitSection
    (k : Type u) [CommRing k] :
    (x0PushedTrivialModule k).sections :=
  PresheafOfModules.sectionsMk
    (fun X => (1 : Γ(x0ChartScheme k, (x0BasicOpen k).ι ⁻¹ᵁ X.unop))) (by
      intro X Y f
      change (x0ChartScheme k).presheaf.map _ 1 = 1
      exact map_one _)

/-- The constant unit section of the second pushed-forward trivial chart
module. -/
noncomputable def x1PushedTrivialUnitSection
    (k : Type u) [CommRing k] :
    (x1PushedTrivialModule k).sections :=
  PresheafOfModules.sectionsMk
    (fun X => (1 : Γ(x1ChartScheme k, (x1BasicOpen k).ι ⁻¹ᵁ X.unop))) (by
      intro X Y f
      change (x1ChartScheme k).presheaf.map _ 1 = 1
      exact map_one _)

/-- The structure-module map selecting the constant unit section on the first
pushed-forward trivial chart module. -/
noncomputable def structureModuleToX0
    (k : Type u) [CommRing k] :
    structureModule k ⟶ x0PushedTrivialModule k :=
  (x0PushedTrivialModule k).unitHomEquiv.symm
    (x0PushedTrivialUnitSection k)

/-- The structure-module map selecting the constant unit section on the second
pushed-forward trivial chart module. -/
noncomputable def structureModuleToX1
    (k : Type u) [CommRing k] :
    structureModule k ⟶ x1PushedTrivialModule k :=
  (x1PushedTrivialModule k).unitHomEquiv.symm
    (x1PushedTrivialUnitSection k)

@[simp]
theorem structureModuleToX0_app_one
    (k : Type u) [CommRing k] (U : (scheme k).Opens) :
    (structureModuleToX0 k).app U (1 : Γ(scheme k, U)) =
      (1 : Γ(x0ChartScheme k, (x0BasicOpen k).ι ⁻¹ᵁ U)) := by
  change (((x0PushedTrivialModule k).unitHomEquiv
    ((x0PushedTrivialModule k).unitHomEquiv.symm
      (x0PushedTrivialUnitSection k))).val (Opposite.op U)) = _
  rw [Equiv.apply_symm_apply]
  rfl

@[simp]
theorem structureModuleToX1_app_one
    (k : Type u) [CommRing k] (U : (scheme k).Opens) :
    (structureModuleToX1 k).app U (1 : Γ(scheme k, U)) =
      (1 : Γ(x1ChartScheme k, (x1BasicOpen k).ι ⁻¹ᵁ U)) := by
  change (((x1PushedTrivialModule k).unitHomEquiv
    ((x1PushedTrivialModule k).unitHomEquiv.symm
      (x1PushedTrivialUnitSection k))).val (Opposite.op U)) = _
  rw [Equiv.apply_symm_apply]
  rfl

@[simp]
theorem x0RestrictionToOverlap_app_one
    (k : Type u) [CommRing k] (U : (scheme k).Opens) :
    (x0RestrictionToOverlap k).app U
        (1 : Γ(x0ChartScheme k, (x0BasicOpen k).ι ⁻¹ᵁ U)) =
      (1 : Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ U)) := by
  change (overlapScheme k).presheaf.map _
      (((overlapToX0 k).appIso _).hom
        ((x0ChartScheme k).presheaf.map _ 1)) = 1
  simp

@[simp]
theorem x1RestrictionToOverlap_app_one
    (k : Type u) [CommRing k] (U : (scheme k).Opens) :
    (x1RestrictionToOverlap k).app U
        (1 : Γ(x1ChartScheme k, (x1BasicOpen k).ι ⁻¹ᵁ U)) =
      (1 : Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ U)) := by
  change (overlapScheme k).presheaf.map _
      (((overlapToX1 k).appIso _).hom
        ((x1ChartScheme k).presheaf.map _ 1)) = 1
  simp

/-- Multiplication by the degree-zero transition factor is the identity on the
trivial overlap module. -/
@[simp]
theorem overlapCoefficientTransitionEnd_zero
    (k : Type u) [CommRing k] :
    overlapCoefficientTransitionEnd k 0 = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change Γ(overlapScheme k, U) at x
  change x * (overlapScheme k).presheaf.map
      (homOfLE (show U ≤ ⊤ from le_top)).op
      (overlapLaurentTopSection k (twistCoefficientTransition k 0)) = x
  simp [overlapLaurentTopSection]

/-- The pushed-forward degree-zero coefficient transition is the identity. -/
@[simp]
theorem pushedOverlapCoefficientTransitionEnd_zero
    (k : Type u) [CommRing k] :
    pushedOverlapCoefficientTransitionEnd k 0 = 𝟙 _ := by
  simp [pushedOverlapCoefficientTransitionEnd]

/-- The two restrictions of the structure module agree on the standard
overlap. -/
theorem structureModule_chart_compatibility
    (k : Type u) [CommRing k] :
    structureModuleToX0 k ≫ x0RestrictionToOverlap k =
      structureModuleToX1 k ≫ x1RestrictionToOverlap k := by
  apply (overlapPushedTrivialModule k).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
  change (x0RestrictionToOverlap k).app U.unop
      ((structureModuleToX0 k).app U.unop
        (1 : Γ(scheme k, U.unop))) =
    (x1RestrictionToOverlap k).app U.unop
      ((structureModuleToX1 k).app U.unop
        (1 : Γ(scheme k, U.unop)))
  rw [structureModuleToX0_app_one k U.unop,
    structureModuleToX1_app_one k U.unop,
    x0RestrictionToOverlap_app_one k U.unop,
    x1RestrictionToOverlap_app_one k U.unop]

/-- The canonical comparison from the structure module to `O(0)`. -/
noncomputable def structureModuleToTwistingSheafZero
    (k : Type u) [CommRing k] :
    structureModule k ⟶ twistingSheaf k 0 :=
  twistingSheafLift k 0 (structureModuleToX0 k) (structureModuleToX1 k) (by
    simpa using structureModule_chart_compatibility k)

@[reassoc]
theorem structureModuleToTwistingSheafZero_toX0
    (k : Type u) [CommRing k] :
    structureModuleToTwistingSheafZero k ≫ twistingSheafToX0 k 0 =
      structureModuleToX0 k := by
  apply twistingSheafLift_toX0

@[reassoc]
theorem structureModuleToTwistingSheafZero_toX1
    (k : Type u) [CommRing k] :
    structureModuleToTwistingSheafZero k ≫ twistingSheafToX1 k 0 =
      structureModuleToX1 k := by
  apply twistingSheafLift_toX1

end

end RiemannRoch.ProjectiveLine
