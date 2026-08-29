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
`O(m+n)`. We sheafify the local products and use the gluing universal property
of the target twisting sheaf to obtain the global multiplication morphism.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Opposite

noncomputable section

universe u

/-- Ordinary multiplication of sections, named explicitly so that the
commutative-ring structure is not obscured by the forgetful functor to
`RingCat`. -/
private def schemeSectionMul (X : Scheme.{u}) (U : X.Opens)
    (x y : Γ(X, U)) : Γ(X, U) :=
  x * y

section TensorConstruction

/-- Sections of a scheme's underlying ring sheaf retain their commutative-ring
structure after forgetting from `CommRingCat` to `RingCat`. -/
local instance (priority := 2000) schemeRingCatSheafCommRing
    (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

set_option backward.isDefEq.respectTransparency false in
/-- The restriction map for the pointwise tensor product of two module
presheaves over a scheme. -/
private noncomputable def modulePresheafTensorObjMap (X : Scheme.{u})
    (M N : X.PresheafOfModules) {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    M.obj U ⊗ N.obj U ⟶
      (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
        (M.obj V ⊗ N.obj V) :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun m n ↦ M.map f m ⊗ₜ N.map f n)
    (by
      intro m m' n
      dsimp +instances
      rw [map_add, TensorProduct.add_tmul])
    (by
      intro a m n
      dsimp
      erw [M.map_smul]
      rfl)
    (by
      intro m n n'
      dsimp +instances
      rw [map_add, TensorProduct.tmul_add])
    (by
      intro a m n
      dsimp
      erw [N.map_smul,
        TensorProduct.tmul_smul (r := X.ringCatSheaf.obj.map f a)]
      rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The pointwise tensor product of two presheaves of modules over a scheme. -/
noncomputable def modulePresheafTensor (X : Scheme.{u})
    (M N : X.PresheafOfModules) : X.PresheafOfModules where
  obj U := M.obj U ⊗ N.obj U
  map f := modulePresheafTensorObjMap X M N f
  map_id U := ModuleCat.MonoidalCategory.tensor_ext (by
    intro m n
    dsimp [modulePresheafTensorObjMap]
    simp)
  map_comp f g := ModuleCat.MonoidalCategory.tensor_ext (by
    intro m n
    dsimp [modulePresheafTensorObjMap]
    simp +instances)

set_option backward.isDefEq.respectTransparency false in
@[simp]
private theorem modulePresheafTensor_map_tmul {X : Scheme.{u}}
    {M N : X.PresheafOfModules} {U V : X.Opensᵒᵖ} (f : U ⟶ V)
    (m : M.obj U) (n : N.obj U) :
    (modulePresheafTensor X M N).map f
        (m ⊗ₜ[X.ringCatSheaf.obj.obj U] n) = M.map f m ⊗ₜ N.map f n :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The pointwise tensor product of two morphisms of module presheaves. -/
private noncomputable def modulePresheafTensorMap {X : Scheme.{u}}
    {M₁ M₂ M₃ M₄ : X.PresheafOfModules}
    (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) :
    modulePresheafTensor X M₁ M₃ ⟶ modulePresheafTensor X M₂ M₄ where
  app U := f.app U ⊗ₘ g.app U
  naturality {U V} h := ModuleCat.MonoidalCategory.tensor_ext (fun m n ↦ by
    change
      (f.app V (M₁.map h m : M₁.obj V)) ⊗ₜ[X.ringCatSheaf.obj.obj V]
          (g.app V (M₃.map h n : M₃.obj V)) =
        (M₂.map h (f.app U m) : M₂.obj V) ⊗ₜ[X.ringCatSheaf.obj.obj V]
          (M₄.map h (g.app U n) : M₄.obj V)
    rw [PresheafOfModules.naturality_apply,
      PresheafOfModules.naturality_apply])

/-- The tensor product of two module sheaves, obtained by sheafifying their
pointwise presheaf tensor product. -/
noncomputable def moduleSheafTensor
    (k : Type u) [CommRing k] (M N : ModuleSheaf k) : ModuleSheaf k :=
  (PresheafOfModules.sheafification
    (𝟙 (scheme k).ringCatSheaf.obj)).obj
      (modulePresheafTensor (scheme k) M.val N.val)

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
      (modulePresheafTensor (scheme k) M.val N.val ⟶
        (PresheafOfModules.restrictScalars
          (𝟙 (scheme k).ringCatSheaf.obj)).obj P.val) :=
  PresheafOfModules.sheafificationHomEquiv
    (𝟙 (scheme k).ringCatSheaf.obj)

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication on one open of a pushed-forward structure module. -/
private noncomputable def pushedStructureMultiplicationApp
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opensᵒᵖ) :
    (((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)).val.obj U) ⊗
      (((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)).val.obj U) ⟶
      ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)).val.obj U :=
  ModuleCat.MonoidalCategory.tensorLift
    (schemeSectionMul X (f ⁻¹ᵁ U.unop))
    (by intros; simp [schemeSectionMul, add_mul])
    (by
      intro a x y
      change @Mul.mul Γ(X, f ⁻¹ᵁ U.unop) inferInstance
          (@Mul.mul Γ(X, f ⁻¹ᵁ U.unop) inferInstance _ x) y =
        @Mul.mul Γ(X, f ⁻¹ᵁ U.unop) inferInstance _
          (@Mul.mul Γ(X, f ⁻¹ᵁ U.unop) inferInstance x y)
      exact mul_assoc _ _ _)
    (by intros; simp [schemeSectionMul, mul_add])
    (by
      intro a x y
      change @Mul.mul Γ(X, f ⁻¹ᵁ U.unop) inferInstance x
          (@Mul.mul Γ(X, f ⁻¹ᵁ U.unop) inferInstance _ y) =
        @Mul.mul Γ(X, f ⁻¹ᵁ U.unop) inferInstance _
          (@Mul.mul Γ(X, f ⁻¹ᵁ U.unop) inferInstance x y)
      exact mul_left_comm _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication on the pushforward of a structure module, expressed on the
pointwise tensor product of its underlying presheaf. -/
private noncomputable def pushedStructureMultiplication
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modulePresheafTensor Y
        ((Scheme.Modules.pushforward f).obj
          (SheafOfModules.unit X.ringCatSheaf)).val
        ((Scheme.Modules.pushforward f).obj
          (SheafOfModules.unit X.ringCatSheaf)).val ⟶
      ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)).val where
  app U := pushedStructureMultiplicationApp f U
  naturality {U V} h := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    change
      schemeSectionMul X (f ⁻¹ᵁ V.unop)
          (X.presheaf.map
            ((TopologicalSpace.Opens.map f.base).map h.unop).op x)
          (X.presheaf.map
            ((TopologicalSpace.Opens.map f.base).map h.unop).op y) =
        X.presheaf.map ((TopologicalSpace.Opens.map f.base).map h.unop).op
          (schemeSectionMul X (f ⁻¹ᵁ U.unop) x y)
    unfold schemeSectionMul
    exact ((X.presheaf.map
      ((TopologicalSpace.Opens.map f.base).map h.unop).op).hom.map_mul
        (show Γ(X, f ⁻¹ᵁ U.unop) from x)
        (show Γ(X, f ⁻¹ᵁ U.unop) from y)).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
private theorem pushedStructureMultiplication_app_tmul
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (x y : Γ(X, f ⁻¹ᵁ U)) :
    (pushedStructureMultiplication f).app (op U)
      (x ⊗ₜ[Γ(Y, U)] y) = schemeSectionMul X (f ⁻¹ᵁ U) x y :=
  by
    change pushedStructureMultiplicationApp f (op U)
      (x ⊗ₜ[Γ(Y, U)] y) = schemeSectionMul X (f ⁻¹ᵁ U) x y
    unfold pushedStructureMultiplicationApp
    apply ModuleCat.MonoidalCategory.tensorLift_tmul

/-- Multiply the two `X₀` coordinates of sections of `O(m)` and `O(n)`. -/
private noncomputable def x0TensorCoordinate
    (k : Type u) [CommRing k] (m n : ℤ) :
    modulePresheafTensor (scheme k)
        (twistingSheaf k m).val (twistingSheaf k n).val ⟶
      (x0PushedTrivialModule k).val :=
  modulePresheafTensorMap
      (twistingSheafToX0 k m).val (twistingSheafToX0 k n).val ≫
    pushedStructureMultiplication (x0BasicOpen k).ι

/-- Multiply the two `X₁` coordinates of sections of `O(m)` and `O(n)`. -/
private noncomputable def x1TensorCoordinate
    (k : Type u) [CommRing k] (m n : ℤ) :
    modulePresheafTensor (scheme k)
        (twistingSheaf k m).val (twistingSheaf k n).val ⟶
      (x1PushedTrivialModule k).val :=
  modulePresheafTensorMap
      (twistingSheafToX1 k m).val (twistingSheafToX1 k n).val ≫
    pushedStructureMultiplication (x1BasicOpen k).ι

/-- Restriction from the first chart to the overlap preserves products. -/
private theorem x0RestrictionToOverlap_app_mul
    (k : Type u) [CommRing k] (U : (scheme k).Opens)
    (x y : Γ(x0ChartScheme k, (x0BasicOpen k).ι ⁻¹ᵁ U)) :
    ((x0RestrictionToOverlap k).app U
        (schemeSectionMul (x0ChartScheme k) ((x0BasicOpen k).ι ⁻¹ᵁ U) x y) :
        Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ U)) =
      schemeSectionMul (overlapScheme k) ((standardOverlap k).ι ⁻¹ᵁ U)
        ((x0RestrictionToOverlap k).app U x)
        ((x0RestrictionToOverlap k).app U y) := by
  change (overlapScheme k).presheaf.map _
      (((overlapToX0 k).appIso _).hom
        ((x0ChartScheme k).presheaf.map _
          (schemeSectionMul (x0ChartScheme k) _ x y))) =
    schemeSectionMul (overlapScheme k) _
      ((overlapScheme k).presheaf.map _
        (((overlapToX0 k).appIso _).hom
          ((x0ChartScheme k).presheaf.map _ x)))
      ((overlapScheme k).presheaf.map _
        (((overlapToX0 k).appIso _).hom
          ((x0ChartScheme k).presheaf.map _ y)))
  simp [schemeSectionMul]

/-- Restriction from the second chart to the overlap preserves products. -/
private theorem x1RestrictionToOverlap_app_mul
    (k : Type u) [CommRing k] (U : (scheme k).Opens)
    (x y : Γ(x1ChartScheme k, (x1BasicOpen k).ι ⁻¹ᵁ U)) :
    ((x1RestrictionToOverlap k).app U
        (schemeSectionMul (x1ChartScheme k) ((x1BasicOpen k).ι ⁻¹ᵁ U) x y) :
        Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ U)) =
      schemeSectionMul (overlapScheme k) ((standardOverlap k).ι ⁻¹ᵁ U)
        ((x1RestrictionToOverlap k).app U x)
        ((x1RestrictionToOverlap k).app U y) := by
  change (overlapScheme k).presheaf.map _
      (((overlapToX1 k).appIso _).hom
        ((x1ChartScheme k).presheaf.map _
          (schemeSectionMul (x1ChartScheme k) _ x y))) =
    schemeSectionMul (overlapScheme k) _
      ((overlapScheme k).presheaf.map _
        (((overlapToX1 k).appIso _).hom
          ((x1ChartScheme k).presheaf.map _ x)))
      ((overlapScheme k).presheaf.map _
        (((overlapToX1 k).appIso _).hom
          ((x1ChartScheme k).presheaf.map _ y)))
  simp [schemeSectionMul]

/-- The pushed-forward overlap transition acts by multiplication by the
restricted Laurent monomial on every open. -/
private theorem pushedOverlapCoefficientTransitionEnd_app_apply
    (k : Type u) [CommRing k] (n : ℤ) (U : (scheme k).Opens)
    (x : Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ U)) :
    (pushedOverlapCoefficientTransitionEnd k n).app U x =
      schemeSectionMul (overlapScheme k) ((standardOverlap k).ι ⁻¹ᵁ U) x
        ((overlapScheme k).presheaf.map
          (homOfLE (show (standardOverlap k).ι ⁻¹ᵁ U ≤ ⊤ from le_top)).op
          (overlapLaurentTopSection k (twistCoefficientTransition k n))) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
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
  let x₀m : Γ(x0ChartScheme k, (x0BasicOpen k).ι ⁻¹ᵁ V) :=
    (twistingSheafToX0 k m).app V x
  let x₀n : Γ(x0ChartScheme k, (x0BasicOpen k).ι ⁻¹ᵁ V) :=
    (twistingSheafToX0 k n).app V y
  let x₁m : Γ(x1ChartScheme k, (x1BasicOpen k).ι ⁻¹ᵁ V) :=
    (twistingSheafToX1 k m).app V x
  let x₁n : Γ(x1ChartScheme k, (x1BasicOpen k).ι ⁻¹ᵁ V) :=
    (twistingSheafToX1 k n).app V y
  let a₀ : Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ V) :=
    (x0RestrictionToOverlap k).app V x₀m
  let b₀ : Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ V) :=
    (x0RestrictionToOverlap k).app V x₀n
  let a₁ : Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ V) :=
    (x1RestrictionToOverlap k).app V x₁m
  let b₁ : Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ V) :=
    (x1RestrictionToOverlap k).app V x₁n
  have hm : a₀ * c m = a₁ := by
    have h :=
      congrArg (fun f ↦ f.app V x) (twistingSheaf_overlap_condition k m)
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
    rw [pushedOverlapCoefficientTransitionEnd_app_apply] at h
    change a₀ * c m = a₁ at h
    exact h
  have hn : b₀ * c n = b₁ := by
    have h :=
      congrArg (fun f ↦ f.app V y) (twistingSheaf_overlap_condition k n)
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
    rw [pushedOverlapCoefficientTransitionEnd_app_apply] at h
    change b₀ * c n = b₁ at h
    exact h
  have hc : c (m + n) = c m * c n := by
    dsimp [c]
    rw [twistCoefficientTransition_add]
    simp [overlapLaurentTopSection]
  change
    (pushedOverlapCoefficientTransitionEnd k (m + n)).app V
        ((x0RestrictionToOverlap k).app V
          (schemeSectionMul (x0ChartScheme k) ((x0BasicOpen k).ι ⁻¹ᵁ V)
            x₀m x₀n)) =
      (x1RestrictionToOverlap k).app V
        (schemeSectionMul (x1ChartScheme k) ((x1BasicOpen k).ι ⁻¹ᵁ V)
          x₁m x₁n)
  have h₀ := x0RestrictionToOverlap_app_mul k V x₀m x₀n
  have h₁ := x1RestrictionToOverlap_app_mul k V x₁m x₁n
  rw [h₁]
  change
    (pushedOverlapCoefficientTransitionEnd k (m + n)).app V
        ((x0RestrictionToOverlap k).app V
          (schemeSectionMul (x0ChartScheme k) ((x0BasicOpen k).ι ⁻¹ᵁ V)
            x₀m x₀n)) =
      a₁ * b₁
  calc
    _ = (pushedOverlapCoefficientTransitionEnd k (m + n)).app V
        (a₀ * b₀) := by
      exact congrArg
        (fun z : Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ V) ↦
          (pushedOverlapCoefficientTransitionEnd k (m + n)).app V z) h₀
    _ = (a₀ * b₀) * c (m + n) := by
      rw [pushedOverlapCoefficientTransitionEnd_app_apply]
      change (a₀ * b₀) * c (m + n) = (a₀ * b₀) * c (m + n)
      rfl
    _ = (a₀ * b₀) * (c m * c n) := by rw [hc]
    _ = (a₀ * c m) * (b₀ * c n) := by
      ac_rfl
    _ = a₁ * b₁ := by rw [hm, hn]

end TensorConstruction

@[reassoc]
private theorem presheafToRestrictScalarsId_naturality
    {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{u} R} (f : M ⟶ N) :
    presheafToRestrictScalarsId M ≫
        (PresheafOfModules.restrictScalars (𝟙 R)).map f =
      f ≫ presheafToRestrictScalarsId N := by
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  rfl

/-- The first chart-coordinate product after sheafifying the pointwise tensor
presheaf. -/
noncomputable def twistingSheafTensorToX0
    (k : Type u) [CommRing k] (m n : ℤ) :
    moduleSheafTensor k (twistingSheaf k m) (twistingSheaf k n) ⟶
      x0PushedTrivialModule k :=
  (moduleSheafTensorHomEquiv k).symm
    (x0TensorCoordinate k m n ≫
      presheafToRestrictScalarsId (x0PushedTrivialModule k).val)

/-- The second chart-coordinate product after sheafifying the pointwise tensor
presheaf. -/
noncomputable def twistingSheafTensorToX1
    (k : Type u) [CommRing k] (m n : ℤ) :
    moduleSheafTensor k (twistingSheaf k m) (twistingSheaf k n) ⟶
      x1PushedTrivialModule k :=
  (moduleSheafTensorHomEquiv k).symm
    (x1TensorCoordinate k m n ≫
      presheafToRestrictScalarsId (x1PushedTrivialModule k).val)

set_option backward.isDefEq.respectTransparency false in
private theorem moduleSheafTensorHomEquiv_comp
    (k : Type u) [CommRing k] {M N P Q : ModuleSheaf k}
    (f : moduleSheafTensor k M N ⟶ P) (g : P ⟶ Q) :
    moduleSheafTensorHomEquiv k (f ≫ g) =
      moduleSheafTensorHomEquiv k f ≫
        (SheafOfModules.forget (scheme k).ringCatSheaf ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (scheme k).ringCatSheaf.obj)).map g := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (scheme k).ringCatSheaf.obj)).homEquiv_naturality_right f g
  change moduleSheafTensorHomEquiv k (f ≫ g) =
    moduleSheafTensorHomEquiv k f ≫
      (SheafOfModules.forget (scheme k).ringCatSheaf ⋙
        PresheafOfModules.restrictScalars
          (𝟙 (scheme k).ringCatSheaf.obj)).map g at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The two sheafified chart-coordinate products satisfy the transition
relation for `O(m+n)`. -/
private theorem twistingSheafTensorCoordinates_compatible
    (k : Type u) [CommRing k] (m n : ℤ) :
    twistingSheafTensorToX0 k m n ≫ x0RestrictionToOverlap k ≫
        pushedOverlapCoefficientTransitionEnd k (m + n) =
      twistingSheafTensorToX1 k m n ≫ x1RestrictionToOverlap k := by
  apply (moduleSheafTensorHomEquiv k).injective
  rw [moduleSheafTensorHomEquiv_comp, moduleSheafTensorHomEquiv_comp]
  simp only [twistingSheafTensorToX0, twistingSheafTensorToX1,
    Equiv.apply_symm_apply]
  change
    (x0TensorCoordinate k m n ≫
        presheafToRestrictScalarsId (x0PushedTrivialModule k).val) ≫
      (PresheafOfModules.restrictScalars
        (𝟙 (scheme k).ringCatSheaf.obj)).map
          (x0RestrictionToOverlap k ≫
            pushedOverlapCoefficientTransitionEnd k (m + n)).val =
    (x1TensorCoordinate k m n ≫
        presheafToRestrictScalarsId (x1PushedTrivialModule k).val) ≫
      (PresheafOfModules.restrictScalars
        (𝟙 (scheme k).ringCatSheaf.obj)).map
          (x1RestrictionToOverlap k).val
  rw [Category.assoc, presheafToRestrictScalarsId_naturality,
    Category.assoc, presheafToRestrictScalarsId_naturality]
  have h := tensorCoordinates_compatible k m n
  change x0TensorCoordinate k m n ≫
      (x0RestrictionToOverlap k ≫
        pushedOverlapCoefficientTransitionEnd k (m + n)).val =
    x1TensorCoordinate k m n ≫ (x1RestrictionToOverlap k).val at h
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ presheafToRestrictScalarsId
      (overlapPushedTrivialModule k).val)
    h

/-- The canonical multiplication morphism of twisting sheaves. -/
noncomputable def twistingSheafMultiplication
    (k : Type u) [CommRing k] (m n : ℤ) :
    moduleSheafTensor k (twistingSheaf k m) (twistingSheaf k n) ⟶
      twistingSheaf k (m + n) :=
  twistingSheafLift k (m + n)
    (twistingSheafTensorToX0 k m n)
    (twistingSheafTensorToX1 k m n)
    (twistingSheafTensorCoordinates_compatible k m n)

/-- The first local coordinate of the multiplication morphism is ordinary
coefficient multiplication. -/
@[reassoc (attr := simp)]
theorem twistingSheafMultiplication_toX0
    (k : Type u) [CommRing k] (m n : ℤ) :
    twistingSheafMultiplication k m n ≫ twistingSheafToX0 k (m + n) =
      twistingSheafTensorToX0 k m n := by
  simp [twistingSheafMultiplication]

/-- The second local coordinate of the multiplication morphism is ordinary
coefficient multiplication. -/
@[reassoc (attr := simp)]
theorem twistingSheafMultiplication_toX1
    (k : Type u) [CommRing k] (m n : ℤ) :
    twistingSheafMultiplication k m n ≫ twistingSheafToX1 k (m + n) =
      twistingSheafTensorToX1 k m n := by
  simp [twistingSheafMultiplication]

end

end RiemannRoch.ProjectiveLine
