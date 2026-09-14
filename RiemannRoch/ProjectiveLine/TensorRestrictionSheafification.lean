/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.TensorRestriction

/-!
# Sheafification and restriction

This file lifts the pointwise tensor/restriction compatibility to the sheafified
module tensor product.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- The presheaf ring morphism underlying restriction along an open immersion. -/
private noncomputable def sheafificationRestrictionRingHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    X.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ Y.ringCatSheaf.obj :=
  Functor.whiskerRight
    ({ app U := (f.appIso U.unop).inv } :
      X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf)
    (forget₂ CommRingCat RingCat)

/-- The sheaf morphism underlying restriction along an open immersion. -/
private noncomputable def restrictionSheafHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    X.ringCatSheaf ⟶
      (f.opensFunctor.sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj
          Y.ringCatSheaf :=
  ⟨sheafificationRestrictionRingHom f⟩

/-- Sheafification after presheaf restriction maps canonically to restriction
after sheafification. -/
private noncomputable def restrictSheafificationComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (P : Y.PresheafOfModules) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pushforward
          (sheafificationRestrictionRingHom f)).obj P) ⟶
      (SheafOfModules.pushforward (restrictionSheafHom f)).obj
        ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).symm
    ((PresheafOfModules.pushforward
      (sheafificationRestrictionRingHom f)).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y.ringCatSheaf.obj)).unit.app P))

set_option backward.isDefEq.respectTransparency false in
private theorem restrictSheafificationComparison_toSheaf
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (P : Y.PresheafOfModules) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map
        (restrictSheafificationComparison f P) =
      (f.opensFunctor.pushforwardContinuousSheafificationCompatibility
        AddCommGrpCat (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology Y)).hom.app P.presheaf := by
  rw [restrictSheafificationComparison,
    PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  apply (CategoryTheory.sheafificationAdjunction
    (Opens.grothendieckTopology X) AddCommGrpCat).homEquiv _ _ |>.injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  change
    Functor.whiskerLeft f.opensFunctor.op
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y.ringCatSheaf.obj)).unit.app P)) = _
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact (f.opensFunctor.toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) P.presheaf).symm

set_option backward.isDefEq.respectTransparency false in
private theorem restrictSheafificationComparison_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (P : Y.PresheafOfModules) :
    IsIso (restrictSheafificationComparison f P) := by
  rw [← isIso_iff_of_reflects_iso
    (restrictSheafificationComparison f P)
    (SheafOfModules.toSheaf X.ringCatSheaf)]
  rw [restrictSheafificationComparison_toSheaf]
  infer_instance

/-- Sheafification commutes with restriction along an open immersion. -/
private noncomputable def restrictSheafificationIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (P : Y.PresheafOfModules) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pushforward
          (sheafificationRestrictionRingHom f)).obj P) ≅
      (SheafOfModules.pushforward (restrictionSheafHom f)).obj
        ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P) := by
  letI : IsIso (restrictSheafificationComparison f P) :=
    restrictSheafificationComparison_isIso f P
  exact asIso (restrictSheafificationComparison f P)

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified tensor product commutes with restriction along an open immersion. -/
noncomputable def restrictSchemeModuleSheafTensorIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.Modules) :
    (Scheme.Modules.restrictFunctor f).obj (schemeModuleSheafTensor Y M N) ≅
      schemeModuleSheafTensor X
        ((Scheme.Modules.restrictFunctor f).obj M)
        ((Scheme.Modules.restrictFunctor f).obj N) := by
  let e₁ :=
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (restrictModulePresheafTensorIso f M N)
  let e₂ :=
    restrictSheafificationIso f (modulePresheafTensor Y M.val N.val)
  exact (e₁ ≪≫ e₂).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse tensor restriction comparison is characterized on pure tensors
by the sheafification universal property. This computes restricted bilinear
maps without unfolding sheafification. -/
theorem restrictSchemeModuleSheafTensorIso_inv_homEquiv_app_tmul
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M N P : Y.Modules) (a : schemeModuleSheafTensor Y M N ⟶ P)
    (U : X.Opens)
    (x : (M.restrict f).val.obj (Opposite.op U))
    (y : (N.restrict f).val.obj (Opposite.op U)) :
    (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
      ((restrictSchemeModuleSheafTensorIso f M N).inv ≫
        (Scheme.Modules.restrictFunctor f).map a)).app (Opposite.op U)
          (x ⊗ₜ[Γ(X, U)] y) =
    (PresheafOfModules.sheafificationHomEquiv (𝟙 Y.ringCatSheaf.obj) a).app
      (Opposite.op (f ''ᵁ U))
        ((show M.val.obj (Opposite.op (f ''ᵁ U)) from x) ⊗ₜ[Γ(Y, f ''ᵁ U)]
          (show N.val.obj (Opposite.op (f ''ᵁ U)) from y)) := by
  change ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
            (restrictModulePresheafTensorIso f M N).hom ≫
          restrictSheafificationComparison f (modulePresheafTensor Y M.val N.val) ≫
          (Scheme.Modules.restrictFunctor f).map a)).app (Opposite.op U) _ = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  change ((restrictModulePresheafTensorIso f M N).hom ≫
      ((PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj))
        (restrictSheafificationComparison f (modulePresheafTensor Y M.val N.val))) ≫
      _).app (Opposite.op U) _ = _
  rw [restrictSheafificationComparison]
  erw [Equiv.apply_symm_apply]
  change _ = ((PresheafOfModules.sheafificationAdjunction
      (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _ a).app _ _
  rw [Adjunction.homEquiv_unit]
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply,
    restrictModulePresheafTensorIso_hom_app_tmul]
  rfl

end

end RiemannRoch.ProjectiveLine
