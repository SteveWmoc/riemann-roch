/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.TwistingSheafMultiplication

/-!
# Unit laws for the project-local tensor product

The sheaf tensor product used for twisting sheaves is defined by sheafifying
the pointwise tensor product of module presheaves. This file records the
corresponding tensor-unit comparison with the structure module.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

noncomputable section

universe u

/-- Before sheafification, tensoring a module presheaf on the left by the
structure module is canonically the identity. -/
noncomputable def modulePresheafTensorLeftUnitor
    (X : Scheme.{u}) (M : X.PresheafOfModules) :
    modulePresheafTensor X (SheafOfModules.unit X.ringCatSheaf).val M ≅ M :=
  PresheafOfModules.isoMk
    (fun U => ModuleCat.MonoidalCategory.leftUnitor (M.obj U))
    (by
      intro U V f
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro r m
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

/-- The structure module is the left tensor unit for the project-local
sheafified tensor product. -/
noncomputable def moduleSheafTensorLeftUnitor
    (k : Type u) [CommRing k] (M : ModuleSheaf k) :
    moduleSheafTensor k (structureModule k) M ≅ M :=
  let S := PresheafOfModules.sheafification
    (𝟙 (scheme k).ringCatSheaf.obj)
  S.mapIso
      (modulePresheafTensorLeftUnitor (scheme k) M.val ≪≫
        presheafRestrictScalarsIdIso M.val) ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (scheme k).ringCatSheaf.obj)).counit.app M)

end

end RiemannRoch.ProjectiveLine
