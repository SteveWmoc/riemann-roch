/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.TwistingSheafZero
import RiemannRoch.ProjectiveLine.TwistingSheafMultiplication

/-!
# Unit laws for the project-local tensor product

The sheaf tensor product used for twisting sheaves is defined by sheafifying
the pointwise tensor product of module presheaves. This file records the
corresponding tensor-unit comparisons with the structure module.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

noncomputable section

universe u

/-- Sections of a scheme's ring sheaf retain their commutative-ring structure
after forgetting from `CommRingCat` to `RingCat`. -/
local instance (priority := 2000) tensorUnitSchemeRingCatSheafCommRing
    (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

/-- Before sheafification, tensoring a module presheaf on the left by the
structure module is canonically the identity. -/
noncomputable def modulePresheafTensorLeftUnitor
    (X : Scheme.{u}) (M : X.PresheafOfModules) :
    modulePresheafTensor X (SheafOfModules.unit X.ringCatSheaf).val M ≅ M :=
  PresheafOfModules.isoMk
    (fun U => leftUnitor (C := ModuleCat (X.ringCatSheaf.obj.obj U)) (M.obj U))
    (by
      intro U V f
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro r m
      change M.map f (r • m) = X.ringCatSheaf.obj.map f r • M.map f m
      exact M.map_smul f r m)

/-- Before sheafification, tensoring a module presheaf on the right by the
structure module is canonically the identity. -/
noncomputable def modulePresheafTensorRightUnitor
    (X : Scheme.{u}) (M : X.PresheafOfModules) :
    modulePresheafTensor X M (SheafOfModules.unit X.ringCatSheaf).val ≅ M :=
  PresheafOfModules.isoMk
    (fun U => rightUnitor (C := ModuleCat (X.ringCatSheaf.obj.obj U)) (M.obj U))
    (by
      intro U V f
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro m r
      change M.map f (r • m) = X.ringCatSheaf.obj.map f r • M.map f m
      exact M.map_smul f r m)

/-- Restriction of scalars along the identity morphism of a ring presheaf is
canonically isomorphic to the identity. -/
noncomputable def presheafRestrictScalarsIdIso
    {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) :
    M ≅ (PresheafOfModules.restrictScalars (𝟙 R)).obj M :=
  PresheafOfModules.isoMk
    (fun X =>
      (ModuleCat.restrictScalarsId'App
        ((𝟙 R : R ⟶ R).app X).hom rfl (M.obj X)).symm)
    (by
      intro X Y f
      ext x
      rfl)

/-- The counit identifying the sheafification of an already-sheaf module with
that module is an isomorphism. -/
private theorem sheafificationCounitApp_isIso
    (k : Type u) [CommRing k] (M : ModuleSheaf k) :
    IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (scheme k).ringCatSheaf.obj)).counit.app M) := by
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.toSheaf (scheme k).ringCatSheaf)]
  simp only [PresheafOfModules.toSheaf_map_sheafificationAdjunction_counit_app]
  infer_instance

/-- The structure module is the left tensor unit for the project-local
sheafified tensor product. -/
noncomputable def moduleSheafTensorLeftUnitor
    (k : Type u) [CommRing k] (M : ModuleSheaf k) :
    moduleSheafTensor k (structureModule k) M ≅ M := by
  let S := PresheafOfModules.sheafification
    (𝟙 (scheme k).ringCatSheaf.obj)
  let c := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (scheme k).ringCatSheaf.obj)).counit.app M
  letI : IsIso c := sheafificationCounitApp_isIso k M
  exact S.mapIso
      (modulePresheafTensorLeftUnitor (scheme k) M.val ≪≫
        presheafRestrictScalarsIdIso M.val) ≪≫
    asIso c

/-- The structure module is the right tensor unit for the project-local
sheafified tensor product. -/
noncomputable def moduleSheafTensorRightUnitor
    (k : Type u) [CommRing k] (M : ModuleSheaf k) :
    moduleSheafTensor k M (structureModule k) ≅ M := by
  let S := PresheafOfModules.sheafification
    (𝟙 (scheme k).ringCatSheaf.obj)
  let c := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (scheme k).ringCatSheaf.obj)).counit.app M
  letI : IsIso c := sheafificationCounitApp_isIso k M
  exact S.mapIso
      (modulePresheafTensorRightUnitor (scheme k) M.val ≪≫
        presheafRestrictScalarsIdIso M.val) ≪≫
    asIso c

end

end RiemannRoch.ProjectiveLine
