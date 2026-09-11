/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.TensorUnit
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Restriction and the sheafified tensor product

This file develops the compatibility between restriction to an open subscheme
and the sheafified tensor product used for twisting sheaves.

The first step is to expose the same tensor construction on an arbitrary
scheme. The existing `moduleSheafTensor` on `P¹_k` is definitionally the
special case of this construction.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory MonoidalCategory
open Functor.LaxMonoidal

noncomputable section

universe u

/-- Sections of the ring sheaf retain their commutative-ring structure after
forgetting from `CommRingCat` to `RingCat`. -/
local instance (priority := 2000) tensorRestrictionSchemeRingCatSheafCommRing
    (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

/-- The sheafified pointwise tensor product of two module sheaves on an
arbitrary scheme. This is the scheme-general form of `moduleSheafTensor`. -/
noncomputable def schemeModuleSheafTensor
    (X : Scheme.{u}) (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification
    (𝟙 X.ringCatSheaf.obj)).obj
      (modulePresheafTensor X M.val N.val)

/-- The projective-line tensor product is exactly the scheme-general tensor
product specialized to `P¹_k`. -/
theorem moduleSheafTensor_eq_schemeModuleSheafTensor
    (k : Type u) [CommRing k] (M N : ModuleSheaf k) :
    moduleSheafTensor k M N = schemeModuleSheafTensor (scheme k) M N :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The tensorator for restriction of scalars along a ring equivalence is
bijective on underlying modules. -/
private theorem restrictScalarsTensorator_bijective
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (M N : ModuleCat.{u} S) :
    Function.Bijective
      (μ (ModuleCat.restrictScalars (e : R →+* S)) M N) := by
  letI : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) :=
    RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) :=
    RingHomInvPair.of_ringEquiv e.symm
  let eM :
      LinearEquiv (σ' := (e.symm : S →+* R)) (e : R →+* S)
        ((ModuleCat.restrictScalars (e : R →+* S)).obj M : Type u)
        (M : Type u) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let eN :
      LinearEquiv (σ' := (e.symm : S →+* R)) (e : R →+* S)
        ((ModuleCat.restrictScalars (e : R →+* S)).obj N : Type u)
        (N : Type u) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let eTensor := TensorProduct.congr eM eN
  have h : ∀ x, μ (ModuleCat.restrictScalars (e : R →+* S)) M N x = eTensor x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
    | tmul m n =>
        simp [eTensor, eM, eN, ModuleCat.restrictScalars_μ_tmul]
  constructor
  · intro x y hxy
    apply eTensor.injective
    rw [← h x, ← h y]
    exact hxy
  · intro y
    obtain ⟨x, hx⟩ := eTensor.surjective y
    exact ⟨x, (h x).trans hx⟩

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of scalars along a ring equivalence preserves tensor products:
its canonical lax-monoidal tensorator is an isomorphism. -/
theorem restrictScalarsTensorator_isIso_of_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (M N : ModuleCat.{u} S) :
    IsIso (μ (ModuleCat.restrictScalars (e : R →+* S)) M N) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact restrictScalarsTensorator_bijective e M N

/-- The morphism of ring-valued presheaves used by restriction along an open
immersion. Its component on an open `U` is the inverse of the canonical ring
isomorphism `Γ(Y, f(U)) ≅ Γ(X, U)`. -/
private noncomputable def restrictionRingHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    X.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ Y.ringCatSheaf.obj :=
  Functor.whiskerRight
    ({ app U := (f.appIso U.unop).inv } :
      X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf)
    (forget₂ CommRingCat RingCat)

/-- On underlying module presheaves, scheme-theoretic restriction is exactly
pushforward by the opens functor followed by restriction of scalars along
`restrictionRingHom`. -/
theorem restrict_val_eq_pushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) :
    ((Scheme.Modules.restrictFunctor f).obj M).val =
      (PresheafOfModules.pushforward (restrictionRingHom f)).obj M.val :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Our project-local pointwise tensor is the tensor object from Mathlib's
monoidal structure on presheaves of modules. -/
private theorem modulePresheafTensor_eq_tensorObj
    (X : Scheme.{u}) (M N : X.PresheafOfModules) :
    modulePresheafTensor X M N =
      PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The componentwise tensorator used to compare tensor product with
restriction along an open immersion. Naming it separately keeps the naturality
proof on Mathlib's stable elementwise API. -/
private noncomputable def restrictionTensoratorIsoApp
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.Modules) (U : X.Opensᵒᵖ) :
    ((Scheme.Modules.restrictFunctor f).obj M).val.obj U ⊗
        ((Scheme.Modules.restrictFunctor f).obj N).val.obj U ≅
      (ModuleCat.restrictScalars ((restrictionRingHom f).app U).hom).obj
        (M.val.obj (f.opensFunctor.op.obj U) ⊗
          N.val.obj (f.opensFunctor.op.obj U)) := by
  let e : (X.presheaf.obj U : Type u) ≃+*
      (Y.presheaf.obj (f.opensFunctor.op.obj U) : Type u) :=
    (f.appIso U.unop).symm.commRingCatIsoToRingEquiv
  have he : ((restrictionRingHom f).app U).hom = e.toRingHom := rfl
  change
    ((ModuleCat.restrictScalars e.toRingHom).obj
        (M.val.obj (f.opensFunctor.op.obj U)) ⊗
      (ModuleCat.restrictScalars e.toRingHom).obj
        (N.val.obj (f.opensFunctor.op.obj U))) ≅
    (ModuleCat.restrictScalars e.toRingHom).obj
      (M.val.obj (f.opensFunctor.op.obj U) ⊗
        N.val.obj (f.opensFunctor.op.obj U))
  letI : IsIso
      (μ (ModuleCat.restrictScalars e.toRingHom)
        (M.val.obj (f.opensFunctor.op.obj U))
        (N.val.obj (f.opensFunctor.op.obj U))) :=
    restrictScalarsTensorator_isIso_of_ringEquiv e _ _
  exact asIso
    (μ (ModuleCat.restrictScalars e.toRingHom)
      (M.val.obj (f.opensFunctor.op.obj U))
      (N.val.obj (f.opensFunctor.op.obj U)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[simp]
private theorem restrictionTensoratorIsoApp_hom_tmul
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.Modules) (U : X.Opensᵒᵖ)
    (m : ((Scheme.Modules.restrictFunctor f).obj M).val.obj U)
    (n : ((Scheme.Modules.restrictFunctor f).obj N).val.obj U) :
    (restrictionTensoratorIsoApp f M N U).hom
        (m ⊗ₜ[X.presheaf.obj U] n) =
      ((show M.val.obj (f.opensFunctor.op.obj U) from m) ⊗ₜ[
          Y.presheaf.obj (f.opensFunctor.op.obj U)]
        (show N.val.obj (f.opensFunctor.op.obj U) from n)) := by
  exact ModuleCat.restrictScalars_μ_tmul
    (f := (f.appIso U.unop).inv.hom)
    (M.val.obj (f.opensFunctor.op.obj U))
    (N.val.obj (f.opensFunctor.op.obj U))
    (show M.val.obj (f.opensFunctor.op.obj U) from m)
    (show N.val.obj (f.opensFunctor.op.obj U) from n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Mathlib's pointwise tensor object commutes with restriction along an open
immersion. -/
private noncomputable def restrictTensorObjIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.Modules) :
    PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
        ((Scheme.Modules.restrictFunctor f).obj M).val
        ((Scheme.Modules.restrictFunctor f).obj N).val ≅
      (PresheafOfModules.pushforward (restrictionRingHom f)).obj
        (PresheafOfModules.Monoidal.tensorObj (R := Y.presheaf) M.val N.val) := by
  refine PresheafOfModules.isoMk
    (fun U ↦ restrictionTensoratorIsoApp f M N U) ?_
  intro U V g
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
  rw [ModuleCat.restrictScalars.map_apply]
  erw [restrictionTensoratorIsoApp_hom_tmul]
  erw [restrictionTensoratorIsoApp_hom_tmul]
  rw [PresheafOfModules.pushforward_obj_map_apply]
  erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
  rw [Scheme.Modules.restrict_map M f g.unop,
    Scheme.Modules.restrict_map N f g.unop]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pointwise tensor product commutes with restriction along an open immersion.
The component on each open is the canonical tensorator for restriction of
scalars; it is invertible because the ring map is an equivalence. -/
noncomputable def restrictModulePresheafTensorIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.Modules) :
    modulePresheafTensor X
        ((Scheme.Modules.restrictFunctor f).obj M).val
        ((Scheme.Modules.restrictFunctor f).obj N).val ≅
      (PresheafOfModules.pushforward (restrictionRingHom f)).obj
        (modulePresheafTensor Y M.val N.val) := by
  rw [modulePresheafTensor_eq_tensorObj X,
    modulePresheafTensor_eq_tensorObj Y]
  exact restrictTensorObjIso f M N

end

end RiemannRoch.ProjectiveLine
