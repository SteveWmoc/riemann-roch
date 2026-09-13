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

end

end RiemannRoch.ProjectiveLine
