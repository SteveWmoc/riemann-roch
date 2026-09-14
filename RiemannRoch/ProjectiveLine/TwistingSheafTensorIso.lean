/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.TensorRestrictionSheafification
import RiemannRoch.ProjectiveLine.StandardChartIso

/-!
# Tensor products of twisting sheaves

The canonical multiplication map `O(m) ⊗ O(n) ⟶ O(m+n)` is an isomorphism.
On each standard chart, the tensor restriction comparison and the chosen
trivializations identify this map with multiplication of two rank-one free
modules. The standard-cover isomorphism criterion then applies globally.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

noncomputable section

universe u

/-- Sections retain their commutative-ring structure after forgetting to `RingCat`. -/
local instance (priority := 2000) tensorIsoSchemeRingCatSheafCommRing
    (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Trivializations of two module sheaves identify their presheaf tensor with
the structure module via coefficient multiplication. -/
private def trivialTensorPresheafIso (X : Scheme.{u}) (M N : X.Modules)
    (eM : M ≅ SheafOfModules.unit X.ringCatSheaf)
    (eN : N ≅ SheafOfModules.unit X.ringCatSheaf) :
    modulePresheafTensor X M.val N.val ≅
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
        (SheafOfModules.unit X.ringCatSheaf).val := by
  letI : MonoidalCategoryStruct X.PresheafOfModules :=
    PresheafOfModules.monoidalCategoryStruct (R := X.presheaf)
  letI : MonoidalCategory X.PresheafOfModules :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  exact tensorIso ((SheafOfModules.forget _).mapIso eM)
      ((SheafOfModules.forget _).mapIso eN) ≪≫
    modulePresheafTensorLeftUnitor X (SheafOfModules.unit X.ringCatSheaf).val ≪≫
    presheafRestrictScalarsIdIso (SheafOfModules.unit X.ringCatSheaf).val

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A sheafified bilinear map between trivial rank-one modules is invertible
when its coefficients are ordinary multiplication. -/
private theorem isIso_of_tensor_homEquiv_eq_mul
    (X : Scheme.{u}) (M N : X.Modules)
    (eM : M ≅ SheafOfModules.unit X.ringCatSheaf)
    (eN : N ≅ SheafOfModules.unit X.ringCatSheaf)
    (a : schemeModuleSheafTensor X M N ⟶ SheafOfModules.unit X.ringCatSheaf)
    (h : ∀ (U : X.Opens) (x : M.val.obj (op U)) (y : N.val.obj (op U)),
      (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj) a).app
          (op U) (x ⊗ₜ[Γ(X, U)] y) =
        (show Γ(X, U) from eM.hom.app U x) *
          (show Γ(X, U) from eN.hom.app U y)) : IsIso a := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have heq : adj.homEquiv _ _ a = (trivialTensorPresheafIso X M N eM eN).hom := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    exact h U.unop x y
  have : IsIso (adj.homEquiv _ _ a) := by rw [heq]; infer_instance
  have ha : a = (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (adj.homEquiv _ _ a) ≫ adj.counit.app _ := by
    simpa only [Equiv.symm_apply_apply] using
      (adj.homEquiv_counit (g := adj.homEquiv _ _ a))
  rw [ha]
  have : IsIso (adj.counit.app (SheafOfModules.unit X.ringCatSheaf)) := by
    change IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.app _)
    infer_instance
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem x0_multiplication_in_trivializations
    (k : Type u) [CommRing k] (m n : ℤ) :
    IsIso ((restrictSchemeModuleSheafTensorIso (x0BasicOpen k).ι
        (twistingSheaf k m) (twistingSheaf k n)).inv ≫
      (Scheme.Modules.restrictFunctor (x0BasicOpen k).ι).map
        (twistingSheafMultiplication k m n) ≫
      (x0TwistingSheafIso k (m + n)).hom) := by
  apply isIso_of_tensor_homEquiv_eq_mul (x0ChartScheme k) _ _
    (x0TwistingSheafIso k m) (x0TwistingSheafIso k n)
  intro U x y
  rw [← Category.assoc]
  have hnat := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (x0ChartScheme k).ringCatSheaf.obj)).homEquiv_naturality_right
      ((restrictSchemeModuleSheafTensorIso (x0BasicOpen k).ι
        (twistingSheaf k m) (twistingSheaf k n)).inv ≫
        (Scheme.Modules.restrictFunctor (x0BasicOpen k).ι).map
          (twistingSheafMultiplication k m n))
      (x0TwistingSheafIso k (m + n)).hom
  erw [hnat]
  change (x0TwistingSheafIso k (m + n)).hom.app U
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 (x0ChartScheme k).ringCatSheaf.obj)
      ((restrictSchemeModuleSheafTensorIso (x0BasicOpen k).ι
        (twistingSheaf k m) (twistingSheaf k n)).inv ≫
        (Scheme.Modules.restrictFunctor (x0BasicOpen k).ι).map
          (twistingSheafMultiplication k m n))).app (op U)
      (x ⊗ₜ[Γ(x0ChartScheme k, U)] y)) = _
  rw [restrictSchemeModuleSheafTensorIso_inv_homEquiv_app_tmul]
  change (x0ChartScheme k).presheaf.map _
    ((twistingSheafToX0 k (m + n)).app _
      ((moduleSheafTensorHomEquiv k (twistingSheafMultiplication k m n)).app _
        (x ⊗ₜ[Γ(scheme k, (x0BasicOpen k).ι ''ᵁ U)] y))) = _
  rw [twistingSheafMultiplication_homEquiv_app_tmul_toX0]
  exact map_mul _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem x1_multiplication_in_trivializations
    (k : Type u) [CommRing k] (m n : ℤ) :
    IsIso ((restrictSchemeModuleSheafTensorIso (x1BasicOpen k).ι
        (twistingSheaf k m) (twistingSheaf k n)).inv ≫
      (Scheme.Modules.restrictFunctor (x1BasicOpen k).ι).map
        (twistingSheafMultiplication k m n) ≫
      (x1TwistingSheafIso k (m + n)).hom) := by
  apply isIso_of_tensor_homEquiv_eq_mul (x1ChartScheme k) _ _
    (x1TwistingSheafIso k m) (x1TwistingSheafIso k n)
  intro U x y
  rw [← Category.assoc]
  have hnat := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (x1ChartScheme k).ringCatSheaf.obj)).homEquiv_naturality_right
      ((restrictSchemeModuleSheafTensorIso (x1BasicOpen k).ι
        (twistingSheaf k m) (twistingSheaf k n)).inv ≫
        (Scheme.Modules.restrictFunctor (x1BasicOpen k).ι).map
          (twistingSheafMultiplication k m n))
      (x1TwistingSheafIso k (m + n)).hom
  erw [hnat]
  change (x1TwistingSheafIso k (m + n)).hom.app U
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 (x1ChartScheme k).ringCatSheaf.obj)
      ((restrictSchemeModuleSheafTensorIso (x1BasicOpen k).ι
        (twistingSheaf k m) (twistingSheaf k n)).inv ≫
        (Scheme.Modules.restrictFunctor (x1BasicOpen k).ι).map
          (twistingSheafMultiplication k m n))).app (op U)
      (x ⊗ₜ[Γ(x1ChartScheme k, U)] y)) = _
  rw [restrictSchemeModuleSheafTensorIso_inv_homEquiv_app_tmul]
  change (x1ChartScheme k).presheaf.map _
    ((twistingSheafToX1 k (m + n)).app _
      ((moduleSheafTensorHomEquiv k (twistingSheafMultiplication k m n)).app _
        (x ⊗ₜ[Γ(scheme k, (x1BasicOpen k).ι ''ᵁ U)] y))) = _
  rw [twistingSheafMultiplication_homEquiv_app_tmul_toX1]
  exact map_mul _ _ _

/-- Multiplication of twisting sheaves is invertible on the first standard chart. -/
theorem x0Restrict_twistingSheafMultiplication_isIso
    (k : Type u) [CommRing k] (m n : ℤ) :
    IsIso ((Scheme.Modules.restrictFunctor (x0BasicOpen k).ι).map
      (twistingSheafMultiplication k m n)) := by
  have h := x0_multiplication_in_trivializations k m n
  rwa [isIso_comp_left_iff, isIso_comp_right_iff] at h

/-- Multiplication of twisting sheaves is invertible on the second standard chart. -/
theorem x1Restrict_twistingSheafMultiplication_isIso
    (k : Type u) [CommRing k] (m n : ℤ) :
    IsIso ((Scheme.Modules.restrictFunctor (x1BasicOpen k).ι).map
      (twistingSheafMultiplication k m n)) := by
  have h := x1_multiplication_in_trivializations k m n
  rwa [isIso_comp_left_iff, isIso_comp_right_iff] at h

/-- The canonical multiplication map `O(m) ⊗ O(n) ⟶ O(m+n)` is an isomorphism. -/
instance twistingSheafMultiplication_isIso
    (k : Type u) [CommRing k] (m n : ℤ) :
    IsIso (twistingSheafMultiplication k m n) :=
  isIso_of_standard_chart_restrictions k _
    (x0Restrict_twistingSheafMultiplication_isIso k m n)
    (x1Restrict_twistingSheafMultiplication_isIso k m n)

/-- The canonical tensor addition formula for twisting sheaves. -/
def twistingSheafTensorIso (k : Type u) [CommRing k] (m n : ℤ) :
    moduleSheafTensor k (twistingSheaf k m) (twistingSheaf k n) ≅
      twistingSheaf k (m + n) :=
  asIso (twistingSheafMultiplication k m n)

/-- The forward map of the tensor addition isomorphism is the original
canonical multiplication map. -/
@[simp]
theorem twistingSheafTensorIso_hom (k : Type u) [CommRing k] (m n : ℤ) :
    (twistingSheafTensorIso k m n).hom = twistingSheafMultiplication k m n := rfl

end

end RiemannRoch.ProjectiveLine
