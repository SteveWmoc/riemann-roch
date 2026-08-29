/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import RiemannRoch.ProjectiveLine.TwistingSheafCoordinates

/-!
# Multiplication of twisting sheaves

This file constructs the canonical multiplication morphism

```text
O(m) ⊗ O(n) ⟶ O(m + n).
```

Mathlib's pinned sheaf-of-modules API does not yet provide a monoidal structure
on sheaves. It does provide the pointwise tensor product of presheaves of
modules and sheafification. We therefore define the tensor product used here by
sheafifying the pointwise tensor product.

On the two standard charts, multiplication is ordinary multiplication of
coefficients. The identity

```text
t^(-m) t^(-n) = t^(-(m+n))
```

shows that these two local products satisfy the transition relation for
`O(m+n)`. The resulting compatible presheaf morphism descends through the
kernel defining the target twisting sheaf and then through sheafification.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Opposite

noncomputable section

universe u

/-- The pointwise monoidal structure on presheaves of modules over a scheme's
underlying commutative-ring presheaf. -/
private noncomputable instance schemePresheafOfModulesMonoidal
    (X : Scheme.{u}) : MonoidalCategory (PresheafOfModules.{u} X.ringCatSheaf.obj) := by
  change MonoidalCategory
    (PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat))
  infer_instance

/-- The tensor product of two module sheaves, obtained by sheafifying their
pointwise presheaf tensor product. -/
noncomputable def moduleSheafTensor
    (k : Type u) [CommRing k] (M N : ModuleSheaf k) : ModuleSheaf k :=
  (PresheafOfModules.sheafification
    (𝟙 (scheme k).ringCatSheaf.obj)).obj (M.val ⊗ N.val)

/-- The identity comparison from a presheaf of modules to its restriction of
scalars along the identity morphism of the base ring presheaf. -/
noncomputable def presheafToRestrictScalarsId
    {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) :
    M ⟶ (PresheafOfModules.restrictScalars (𝟙 R)).obj M where
  app X := by
    change M.obj X ⟶
      (ModuleCat.restrictScalars ((𝟙 R : R ⟶ R).app X).hom).obj (M.obj X)
    exact (ModuleCat.restrictScalarsId'App
      ((𝟙 R : R ⟶ R).app X).hom rfl (M.obj X)).inv
  naturality {_ _} _ := by
    ext x
    rfl

/-- The sheafification universal property specialized to the tensor product of
two module sheaves. -/
noncomputable def moduleSheafTensorHomEquiv
    (k : Type u) [CommRing k] {M N P : ModuleSheaf k} :
    (moduleSheafTensor k M N ⟶ P) ≃
      (M.val ⊗ N.val ⟶
        (PresheafOfModules.restrictScalars
          (𝟙 (scheme k).ringCatSheaf.obj)).obj P.val) :=
  PresheafOfModules.sheafificationHomEquiv
    (𝟙 (scheme k).ringCatSheaf.obj)

/-- Multiplication on the pushforward of a structure module, expressed on the
pointwise tensor product of its underlying presheaf. -/
private noncomputable def pushedStructureMultiplication
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((Scheme.Modules.pushforward f).obj
          (SheafOfModules.unit X.ringCatSheaf)).val ⊗
        ((Scheme.Modules.pushforward f).obj
          (SheafOfModules.unit X.ringCatSheaf)).val ⟶
      ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)).val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun x y ↦ x * y)
    (by intros; simp [add_mul])
    (by intros; simp [mul_assoc])
    (by intros; simp [mul_add])
    (by intros; simp [mul_assoc, mul_left_comm, mul_comm])
  naturality {_ _} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    change _ = _
    simp

@[simp]
private theorem pushedStructureMultiplication_app_tmul
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (x y : Γ(X, f ⁻¹ᵁ U)) :
    (pushedStructureMultiplication f).app (op U)
      (x ⊗ₜ[Γ(Y, U)] y) = x * y :=
  rfl

/-- Multiply the two `X₀` coordinates of sections of `O(m)` and `O(n)`. -/
private noncomputable def x0TensorCoordinate
    (k : Type u) [CommRing k] (m n : ℤ) :
    (twistingSheaf k m).val ⊗ (twistingSheaf k n).val ⟶
      (x0PushedTrivialModule k).val :=
  ((twistingSheafToX0 k m).val ⊗ₘ (twistingSheafToX0 k n).val) ≫
    pushedStructureMultiplication (x0BasicOpen k).ι

/-- Multiply the two `X₁` coordinates of sections of `O(m)` and `O(n)`. -/
private noncomputable def x1TensorCoordinate
    (k : Type u) [CommRing k] (m n : ℤ) :
    (twistingSheaf k m).val ⊗ (twistingSheaf k n).val ⟶
      (x1PushedTrivialModule k).val :=
  ((twistingSheafToX1 k m).val ⊗ₘ (twistingSheafToX1 k n).val) ≫
    pushedStructureMultiplication (x1BasicOpen k).ι

/-- Restriction from the first chart to the overlap preserves products. -/
private theorem x0RestrictionToOverlap_app_mul
    (k : Type u) [CommRing k] (U : (scheme k).Opens)
    (x y : Γ(x0ChartScheme k, (x0BasicOpen k).ι ⁻¹ᵁ U)) :
    ((x0RestrictionToOverlap k).app U (x * y) :
        Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ U)) =
      ((x0RestrictionToOverlap k).app U x :
          Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ U)) *
        ((x0RestrictionToOverlap k).app U y :
          Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ U)) := by
  change (overlapScheme k).presheaf.map _
      (((overlapToX0 k).appIso _).hom
        ((x0ChartScheme k).presheaf.map _ (x * y))) = _
  simp

/-- Restriction from the second chart to the overlap preserves products. -/
private theorem x1RestrictionToOverlap_app_mul
    (k : Type u) [CommRing k] (U : (scheme k).Opens)
    (x y : Γ(x1ChartScheme k, (x1BasicOpen k).ι ⁻¹ᵁ U)) :
    ((x1RestrictionToOverlap k).app U (x * y) :
        Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ U)) =
      ((x1RestrictionToOverlap k).app U x :
          Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ U)) *
        ((x1RestrictionToOverlap k).app U y :
          Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ U)) := by
  change (overlapScheme k).presheaf.map _
      (((overlapToX1 k).appIso _).hom
        ((x1ChartScheme k).presheaf.map _ (x * y))) = _
  simp

/-- The pushed-forward overlap transition acts by multiplication by the
restricted Laurent monomial on every open. -/
private theorem pushedOverlapCoefficientTransitionEnd_app_apply
    (k : Type u) [CommRing k] (n : ℤ) (U : (scheme k).Opens)
    (x : Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ U)) :
    (pushedOverlapCoefficientTransitionEnd k n).app U x =
      x * (overlapScheme k).presheaf.map
        (homOfLE (show (standardOverlap k).ι ⁻¹ᵁ U ≤ ⊤ from le_top)).op
        (overlapLaurentTopSection k (twistCoefficientTransition k n)) :=
  rfl

/-- The two coefficientwise products obey the transition relation for
`O(m+n)`. -/
private theorem tensorCoordinates_compatible
    (k : Type u) [CommRing k] (m n : ℤ) :
    x0TensorCoordinate k m n ≫ (x0RestrictionToOverlap k).val ≫
        (pushedOverlapCoefficientTransitionEnd k (m + n)).val =
      x1TensorCoordinate k m n ≫ (x1RestrictionToOverlap k).val := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  let V := U.unop
  let c : ℤ → Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ V) := fun q ↦
    (overlapScheme k).presheaf.map
      (homOfLE (show (standardOverlap k).ι ⁻¹ᵁ V ≤ ⊤ from le_top)).op
      (overlapLaurentTopSection k (twistCoefficientTransition k q))
  let a₀ := (x0RestrictionToOverlap k).app V
    ((twistingSheafToX0 k m).app V x)
  let b₀ := (x0RestrictionToOverlap k).app V
    ((twistingSheafToX0 k n).app V y)
  let a₁ := (x1RestrictionToOverlap k).app V
    ((twistingSheafToX1 k m).app V x)
  let b₁ := (x1RestrictionToOverlap k).app V
    ((twistingSheafToX1 k n).app V y)
  have hm : a₀ * c m = a₁ := by
    simpa [a₀, a₁, c, Scheme.Modules.Hom.comp_app,
      pushedOverlapCoefficientTransitionEnd_app_apply] using
      congrArg (fun f ↦ f.app V x) (twistingSheaf_overlap_condition k m)
  have hn : b₀ * c n = b₁ := by
    simpa [b₀, b₁, c, Scheme.Modules.Hom.comp_app,
      pushedOverlapCoefficientTransitionEnd_app_apply] using
      congrArg (fun f ↦ f.app V y) (twistingSheaf_overlap_condition k n)
  have hc : c (m + n) = c m * c n := by
    dsimp [c]
    rw [twistCoefficientTransition_add]
    simp [overlapLaurentTopSection]
  change
    (pushedOverlapCoefficientTransitionEnd k (m + n)).app V
        ((x0RestrictionToOverlap k).app V
          ((twistingSheafToX0 k m).app V x *
            (twistingSheafToX0 k n).app V y)) =
      (x1RestrictionToOverlap k).app V
        ((twistingSheafToX1 k m).app V x *
          (twistingSheafToX1 k n).app V y)
  rw [x0RestrictionToOverlap_app_mul, x1RestrictionToOverlap_app_mul,
    pushedOverlapCoefficientTransitionEnd_app_apply]
  change (a₀ * b₀) * c (m + n) = a₁ * b₁
  rw [hc]
  calc
    (a₀ * b₀) * (c m * c n) = (a₀ * c m) * (b₀ * c n) := by
      ac_rfl
    _ = a₁ * b₁ := by rw [hm, hn]

/-- The coefficientwise product as a morphism from the pointwise tensor
presheaf to the underlying presheaf of `O(m+n)`. -/
noncomputable def twistingSheafMultiplicationPresheaf
    (k : Type u) [CommRing k] (m n : ℤ) :
    (twistingSheaf k m).val ⊗ (twistingSheaf k n).val ⟶
      (twistingSheaf k (m + n)).val := by
  let R := (scheme k).ringCatSheaf
  let F := SheafOfModules.forget R
  let A := x0PushedTrivialModule k
  let B := x1PushedTrivialModule k
  let D := overlapPushedTrivialModule k
  let f₀ := x0TensorCoordinate k m n
  let f₁ := x1TensorCoordinate k m n
  letI : F.Additive := inferInstance
  letI : PreservesFiniteBiproducts F :=
    Functor.preservesFiniteBiproductsOfAdditive F
  letI : PreservesBinaryBiproduct A B F :=
    preservesBinaryBiproduct_of_preservesBiproduct F A B
  let e := F.mapBiprod A B
  let h : F.obj A ⊞ F.obj B ⟶ F.obj D :=
    biprod.desc
      (F.map (x0RestrictionToOverlap k ≫
        pushedOverlapCoefficientTransitionEnd k (m + n)))
      (-F.map (x1RestrictionToOverlap k))
  have hmap : F.map (twistingCompatibilityMap k (m + n)) = e.hom ≫ h := by
    dsimp [e, h, twistingCompatibilityMap]
    simpa using
      (biprod.mapBiprod_hom_desc (F := F) A B
        (x0RestrictionToOverlap k ≫
          pushedOverlapCoefficientTransitionEnd k (m + n))
        (-x1RestrictionToOverlap k)).symm
  let p : (twistingSheaf k m).val ⊗ (twistingSheaf k n).val ⟶
      F.obj (A ⊞ B) := biprod.lift f₀ f₁ ≫ e.inv
  have hp : p ≫ F.map (twistingCompatibilityMap k (m + n)) = 0 := by
    rw [hmap]
    dsimp [p]
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    dsimp [h, f₀, f₁]
    simpa [sub_eq_add_neg, Category.assoc] using
      sub_eq_zero.mpr (tensorCoordinates_compatible k m n)
  let c : KernelFork (twistingCompatibilityMap k (m + n)) :=
    KernelFork.ofι (kernel.ι (twistingCompatibilityMap k (m + n)))
      (kernel.condition (twistingCompatibilityMap k (m + n)))
  have hc : IsLimit c := kernelIsKernel (twistingCompatibilityMap k (m + n))
  have hcF : IsLimit (c.map F) := c.mapIsLimit hc F
  let s : KernelFork (F.map (twistingCompatibilityMap k (m + n))) :=
    KernelFork.ofι p hp
  exact hcF.lift s

/-- The canonical multiplication morphism of twisting sheaves. -/
noncomputable def twistingSheafMultiplication
    (k : Type u) [CommRing k] (m n : ℤ) :
    moduleSheafTensor k (twistingSheaf k m) (twistingSheaf k n) ⟶
      twistingSheaf k (m + n) :=
  (moduleSheafTensorHomEquiv k).symm
    (twistingSheafMultiplicationPresheaf k m n ≫
      presheafToRestrictScalarsId (twistingSheaf k (m + n)).val)

/-- The multiplication morphism is characterized by the coefficientwise
product before sheafification. -/
theorem moduleSheafTensorHomEquiv_twistingSheafMultiplication
    (k : Type u) [CommRing k] (m n : ℤ) :
    moduleSheafTensorHomEquiv k (twistingSheafMultiplication k m n) =
      twistingSheafMultiplicationPresheaf k m n ≫
        presheafToRestrictScalarsId (twistingSheaf k (m + n)).val := by
  simp [twistingSheafMultiplication]

end

end RiemannRoch.ProjectiveLine
