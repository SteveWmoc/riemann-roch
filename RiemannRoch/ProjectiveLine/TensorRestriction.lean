/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.TensorUnit
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

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

end

end RiemannRoch.ProjectiveLine
