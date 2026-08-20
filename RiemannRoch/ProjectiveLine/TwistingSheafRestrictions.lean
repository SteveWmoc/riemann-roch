/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import RiemannRoch.ProjectiveLine.TwistingSheafCoordinates

/-!
# Standard-chart restrictions of twisting sheaves

This file develops the restriction isomorphisms for the twisting sheaf `O(n)`
on the two standard affine charts of `P¹_k`.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

/-- Restriction along an open immersion is additive. -/
private theorem restrictFunctor_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : (Scheme.Modules.restrictFunctor f).Additive := by
  constructor
  intro M N φ ψ
  apply Scheme.Modules.hom_ext
  intro U
  rfl

/-- A module-presheaf map induced by equality of opens is an isomorphism. -/
private instance presheafMapEqToHom_isIso
    {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (e : U = V) :
    IsIso (M.presheaf.map (eqToHom e).op) := by
  cases e
  infer_instance

/-- Restriction to the first standard chart preserves the kernel diagram used
to define `O(n)`.

Mathlib's restriction functor for module sheaves is implemented pointwise by
precomposition on opens followed by restriction of scalars. Both operations
preserve limits, although that composite preservation instance is not currently
registered. -/
theorem x0Restrict_preserves_twisting_kernel
    (k : Type u) [CommRing k] (n : ℤ) :
    PreservesLimit (parallelPair (twistingCompatibilityMap k n) 0)
      (Scheme.Modules.restrictFunctor (x0BasicOpen k).ι) := by
  let j := (x0BasicOpen k).ι
  let F := Scheme.Modules.restrictFunctor j
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit _)
  apply isLimitOfReflects (SheafOfModules.forget _)
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro U
  let K := parallelPair (twistingCompatibilityMap k n) 0
  let X := Opposite.op (j.opensFunctor.obj U.unop)
  let E := SheafOfModules.evaluation (scheme k).ringCatSheaf X
  let hE : PreservesLimit K E :=
    SheafOfModules.evaluationPreservesLimit K X
  have hEval : IsLimit (E.mapCone (limit.cone K)) :=
    (hE.preserves (limit.isLimit K)).some
  change IsLimit
    ((ModuleCat.restrictScalars ((j.appIso U.unop).inv.hom)).mapCone
      (E.mapCone (limit.cone K)))
  exact isLimitOfPreserves _ hEval

/-- On an open contained in the range of an open immersion, the unit of the
restriction--pushforward adjunction is an isomorphism on sections. -/
private theorem restrictAdjunction_unit_app_isIso_of_le_range
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    IsIso (((Scheme.Modules.restrictAdjunction f).unit.app M).app U) := by
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  have hEq : f ''ᵁ f ⁻¹ᵁ U = U := by
    rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hU]
  have hHom : homOfLE (f.image_preimage_le U) = eqToHom hEq :=
    Subsingleton.elim _ _
  rw [hHom]
  exact presheafMapEqToHom_isIso M hEq

/-- An open of the `X0` chart, pulled back to the `X1` chart, lies in the
standard overlap. -/
private theorem x0_image_preimage_x1_le_overlapRange
    (k : Type u) [CommRing k] (U : (x0ChartScheme k).Opens) :
    (x1BasicOpen k).ι ⁻¹ᵁ ((x0BasicOpen k).ι ''ᵁ U) ≤
      (overlapToX1 k).opensRange := by
  let j0 := (x0BasicOpen k).ι
  let j1 := (x1BasicOpen k).ι
  let r := overlapToX1 k
  let W := j1 ⁻¹ᵁ (j0 ''ᵁ U)
  apply (j1.image_le_image_iff W r.opensRange).mp
  calc
    j1 ''ᵁ W = j1.opensRange ⊓ (j0 ''ᵁ U) :=
      j1.image_preimage_eq_opensRange_inf _
    _ ≤ j1.opensRange ⊓ j0.opensRange :=
      inf_le_inf le_rfl (j0.image_le_opensRange U)
    _ = standardOverlap k := by
      simp [j0, j1, standardOverlap, inf_comm]
    _ = j1 ''ᵁ r.opensRange := by
      have hcomp : r ≫ j1 = (standardOverlap k).ι := by
        simp [r, j1, standardOverlap]
      calc
        standardOverlap k = (r ≫ j1).opensRange := by
          apply Opens.ext
          change (standardOverlap k : Set (scheme k)) = Set.range (r ≫ j1)
          rw [hcomp]
          exact (Scheme.Opens.range_ι (standardOverlap k)).symm
        _ = j1 ''ᵁ r.opensRange := Scheme.Hom.opensRange_comp r j1

/-- After restriction to the `X0` chart, the `X1`-to-overlap restriction map
is an isomorphism. Geometrically, every point of `X1` visible inside `X0`
already lies in `X0 ∩ X1`. -/
theorem x0Restrict_x1RestrictionToOverlap_isIso
    (k : Type u) [CommRing k] :
    IsIso ((Scheme.Modules.restrictFunctor (x0BasicOpen k).ι).map
      (x1RestrictionToOverlap k)) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  let j0 := (x0BasicOpen k).ι
  let j1 := (x1BasicOpen k).ι
  let r := overlapToX1 k
  let O1 := x1TrivialModule k
  let W := j1 ⁻¹ᵁ (j0 ''ᵁ U)
  have hW : W ≤ r.opensRange := x0_image_preimage_x1_le_overlapRange k U
  letI : IsIso (((Scheme.Modules.restrictAdjunction r).unit.app O1).app W) :=
    restrictAdjunction_unit_app_isIso_of_le_range r O1 W hW
  change IsIso ((x1RestrictionToOverlap k).app (j0 ''ᵁ U))
  dsimp [x1RestrictionToOverlap]
  infer_instance

end

end RiemannRoch.ProjectiveLine
