/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.TwistingSheafRestrictions

/-!
# The second standard-chart trivialization of twisting sheaves

This file proves the trivialization of `O(n)` on the second standard affine
chart `D_+(X₁)`. It is the companion to the `X₀` trivialization developed in
`TwistingSheafRestrictions`.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

noncomputable section

universe u v

/-- Restriction along an open immersion is additive. -/
private theorem restrictFunctor_additive' {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : (Scheme.Modules.restrictFunctor f).Additive := by
  constructor
  intro M N φ ψ
  apply Scheme.Modules.hom_ext
  intro U
  rfl

/-- The map on sections of an isomorphism of module sheaves is an isomorphism. -/
private theorem modulesHom_app_isIso'
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (hf : IsIso f) (U : X.Opens) :
    IsIso (f.app U) := by
  letI : IsIso f := hf
  exact (Scheme.Modules.Hom.isIso_iff_isIso_app).mp hf U

/-- A module-presheaf map induced by equality of opens is an isomorphism. -/
private instance presheafMapEqToHom_isIso'
    {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (e : U = V) :
    IsIso (M.presheaf.map (eqToHom e).op) := by
  cases e
  change IsIso (M.presheaf.map (𝟙 (Opposite.op U)))
  rw [M.presheaf.map_id]
  infer_instance

/-- On an open contained in the range of an open immersion, the unit of the
restriction--pushforward adjunction is an isomorphism on sections. -/
private theorem restrictAdjunction_unit_app_isIso_of_le_range'
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    IsIso (((Scheme.Modules.restrictAdjunction f).unit.app M).app U) := by
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  have hEq : f ''ᵁ f ⁻¹ᵁ U = U := by
    rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hU]
  have hHom : homOfLE (f.image_preimage_le U) = eqToHom hEq :=
    Subsingleton.elim _ _
  rw [hHom]
  exact presheafMapEqToHom_isIso' M hEq

/-- Restriction to the second standard chart preserves the kernel diagram used
to define `O(n)`. -/
theorem x1Restrict_preserves_twisting_kernel
    (k : Type u) [CommRing k] (n : ℤ) :
    PreservesLimit (parallelPair (twistingCompatibilityMap k n) 0)
      (Scheme.Modules.restrictFunctor (x1BasicOpen k).ι) := by
  let j := (x1BasicOpen k).ι
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

/-- An open of the `X1` chart, pulled back to the `X0` chart, lies in the
standard overlap. -/
private theorem x1_image_preimage_x0_le_overlapRange
    (k : Type u) [CommRing k] (U : (x1ChartScheme k).Opens) :
    (x0BasicOpen k).ι ⁻¹ᵁ ((x1BasicOpen k).ι ''ᵁ U) ≤
      (overlapToX0 k).opensRange := by
  let j0 := (x0BasicOpen k).ι
  let j1 := (x1BasicOpen k).ι
  let r := overlapToX0 k
  let W := j0 ⁻¹ᵁ (j1 ''ᵁ U)
  apply (j0.image_le_image_iff W r.opensRange).mp
  calc
    j0 ''ᵁ W = j0.opensRange ⊓ (j1 ''ᵁ U) :=
      j0.image_preimage_eq_opensRange_inf _
    _ ≤ j0.opensRange ⊓ j1.opensRange :=
      inf_le_inf le_rfl (j1.image_le_opensRange U)
    _ = standardOverlap k := by
      simp [j0, j1, standardOverlap]
    _ = j0 ''ᵁ r.opensRange := by
      have hcomp : r ≫ j0 = (standardOverlap k).ι := by
        simp [r, j0, standardOverlap]
      calc
        standardOverlap k = (r ≫ j0).opensRange := by
          apply Opens.ext
          change (standardOverlap k : Set (scheme k)) = Set.range (r ≫ j0)
          rw [hcomp]
          exact (Scheme.Opens.range_ι (standardOverlap k)).symm
        _ = j0 ''ᵁ r.opensRange := Scheme.Hom.opensRange_comp r j0

/-- After restriction to the `X1` chart, the `X0`-to-overlap restriction map
is an isomorphism. -/
theorem x1Restrict_x0RestrictionToOverlap_isIso
    (k : Type u) [CommRing k] :
    IsIso ((Scheme.Modules.restrictFunctor (x1BasicOpen k).ι).map
      (x0RestrictionToOverlap k)) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  let j1 := (x1BasicOpen k).ι
  change IsIso ((x0RestrictionToOverlap k).app (j1 ''ᵁ U))
  dsimp [x0RestrictionToOverlap]
  refine IsIso.comp_isIso' ?_ ?_
  · refine IsIso.comp_isIso' ?_ ?_
    · exact restrictAdjunction_unit_app_isIso_of_le_range'
        (overlapToX0 k) (x0TrivialModule k)
        ((x0BasicOpen k).ι ⁻¹ᵁ (j1 ''ᵁ U))
        (x1_image_preimage_x0_le_overlapRange k U)
    · exact modulesHom_app_isIso' _
        ((Scheme.Modules.pushforward (overlapToX0 k)).mapIso
          (Scheme.Modules.restrictUnitIso (overlapToX0 k))).isIso_hom _
  · refine IsIso.comp_isIso' ?_ ?_
    · exact modulesHom_app_isIso' _
        ((Scheme.Modules.pushforwardComp (overlapToX0 k) (x0BasicOpen k).ι).app
          (overlapTrivialModule k)).isIso_hom _
    · exact inferInstance

/-- In a preadditive category, the kernel of `(a, b) ↦ f(a) - g(b)` is the
graph of `f⁻¹g` whenever `f` is an isomorphism. In particular its second
projection is an isomorphism. -/
private theorem kernelFork_snd_isIso_of_isLimit_desc_neg
    {C : Type u} [Category.{v} C] [Preadditive C]
    {A B D : C} [HasBinaryBiproduct A B]
    (f : A ⟶ D) (g : B ⟶ D) [IsIso f]
    (c : KernelFork (biprod.desc f (-g))) (hc : IsLimit c) :
    IsIso (c.ι ≫ biprod.snd) := by
  let s : KernelFork (biprod.desc f (-g)) :=
    KernelFork.ofι (biprod.lift (g ≫ inv f) (𝟙 B)) (by
      simp [Category.assoc])
  let l : B ⟶ c.pt := hc.lift s
  have hfg : c.ι ≫ biprod.fst ≫ f = c.ι ≫ biprod.snd ≫ g := by
    have hzero : c.ι ≫ biprod.fst ≫ f - c.ι ≫ biprod.snd ≫ g = 0 := by
      simpa [biprod.desc_eq, sub_eq_add_neg, Category.assoc] using c.condition
    exact sub_eq_zero.mp hzero
  have hfst : c.ι ≫ biprod.fst = c.ι ≫ biprod.snd ≫ g ≫ inv f := by
    rw [← cancel_mono f]
    simpa [Category.assoc] using hfg
  refine ⟨⟨l, ?_, ?_⟩⟩
  · apply Fork.IsLimit.hom_ext hc
    simp only [Category.assoc, Category.id_comp]
    rw [show l ≫ c.ι = s.ι from hc.fac s WalkingParallelPair.zero]
    apply biprod.hom_ext
    · simpa [s, Category.assoc] using hfst.symm
    · simp [s, Category.assoc]
  · rw [← Category.assoc, show l ≫ c.ι = s.ι from hc.fac s WalkingParallelPair.zero]
    simp [s]

/-- The Laurent-polynomial realization of overlap sections respects
multiplication on the top open. -/
private theorem overlapLaurentTopSection_mul'
    (k : Type u) [CommRing k] (f g : LaurentPolynomial k) :
    overlapLaurentTopSection k f * overlapLaurentTopSection k g =
      overlapLaurentTopSection k (f * g) := by
  simp [overlapLaurentTopSection]

/-- On every open of the overlap, the transition endomorphism acts by
multiplication by the restricted Laurent transition section. -/
private theorem overlapCoefficientTransitionEnd_app_apply
    (k : Type u) [CommRing k] (n : ℤ) (U : (overlapScheme k).Opens)
    (x : Γ(overlapScheme k, U)) :
    (overlapCoefficientTransitionEnd k n).app U x =
      x * (overlapScheme k).presheaf.map
        (homOfLE (show U ≤ ⊤ from le_top)).op
        (overlapLaurentTopSection k (twistCoefficientTransition k n)) := by
  rfl

/-- Multiplication by the coefficient transition `t^(-n)` is an automorphism
of the trivial module sheaf on the standard overlap. -/
theorem overlapCoefficientTransitionEnd_isIso
    (k : Type u) [CommRing k] (n : ℤ) :
    IsIso (overlapCoefficientTransitionEnd k n) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  let ρ := (overlapScheme k).presheaf.map
    (homOfLE (show U ≤ ⊤ from le_top)).op
  let a := ρ (overlapLaurentTopSection k (twistCoefficientTransition k n))
  let b := ρ (overlapLaurentTopSection k (twistCoefficientTransition k (-n)))
  have hab : a * b = 1 := by
    dsimp [a, b, ρ]
    rw [← map_mul, overlapLaurentTopSection_mul']
    simp [twistCoefficientTransition, overlapLaurentTopSection]
  have hba : b * a = 1 := by
    rw [mul_comm, hab]
  refine ⟨⟨(overlapCoefficientTransitionEnd k (-n)).app U, ?_, ?_⟩⟩
  · ext x
    change (overlapCoefficientTransitionEnd k (-n)).app U
      ((overlapCoefficientTransitionEnd k n).app U x) = x
    rw [overlapCoefficientTransitionEnd_app_apply,
      overlapCoefficientTransitionEnd_app_apply]
    dsimp [a, b, ρ] at hab ⊢
    rw [mul_assoc, hab, mul_one]
  · ext x
    change (overlapCoefficientTransitionEnd k n).app U
      ((overlapCoefficientTransitionEnd k (-n)).app U x) = x
    rw [overlapCoefficientTransitionEnd_app_apply,
      overlapCoefficientTransitionEnd_app_apply]
    dsimp [a, b, ρ] at hba ⊢
    rw [mul_assoc, hba, mul_one]

/-- The pushed-forward coefficient transition is an automorphism of the
pushed-forward trivial overlap module. -/
theorem pushedOverlapCoefficientTransitionEnd_isIso
    (k : Type u) [CommRing k] (n : ℤ) :
    IsIso (pushedOverlapCoefficientTransitionEnd k n) := by
  letI : IsIso (overlapCoefficientTransitionEnd k n) :=
    overlapCoefficientTransitionEnd_isIso k n
  dsimp [pushedOverlapCoefficientTransitionEnd]
  infer_instance

/-- The canonical `X1` coordinate of `O(n)` becomes an isomorphism after
restriction to the second standard chart. -/
theorem x1Restrict_twistingSheafToX1_isIso
    (k : Type u) [CommRing k] (n : ℤ) :
    IsIso ((Scheme.Modules.restrictFunctor (x1BasicOpen k).ι).map
      (twistingSheafToX1 k n)) := by
  let F := Scheme.Modules.restrictFunctor (x1BasicOpen k).ι
  let A := x0PushedTrivialModule k
  let B := x1PushedTrivialModule k
  let D := overlapPushedTrivialModule k
  let f : A ⟶ D :=
    x0RestrictionToOverlap k ≫ pushedOverlapCoefficientTransitionEnd k n
  let g : B ⟶ D := x1RestrictionToOverlap k
  letI : F.Additive := restrictFunctor_additive' (x1BasicOpen k).ι
  letI : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  letI : PreservesBinaryBiproduct A B F :=
    preservesBinaryBiproduct_of_preservesBiproduct F A B
  letI : PreservesLimit (parallelPair (twistingCompatibilityMap k n) 0) F :=
    x1Restrict_preserves_twisting_kernel k n
  letI : IsIso (F.map (x0RestrictionToOverlap k)) :=
    x1Restrict_x0RestrictionToOverlap_isIso k
  letI : IsIso (pushedOverlapCoefficientTransitionEnd k n) :=
    pushedOverlapCoefficientTransitionEnd_isIso k n
  letI : IsIso (F.map f) := by
    dsimp [f]
    rw [Functor.map_comp]
    infer_instance
  let e := F.mapBiprod A B
  let h : F.obj A ⊞ F.obj B ⟶ F.obj D :=
    biprod.desc (F.map f) (-F.map g)
  have hmap : F.map (twistingCompatibilityMap k n) = e.hom ≫ h := by
    dsimp [e, h, f, g, twistingCompatibilityMap]
    simpa using
      (biprod.mapBiprod_hom_desc (F := F) A B
        (x0RestrictionToOverlap k ≫ pushedOverlapCoefficientTransitionEnd k n)
        (-x1RestrictionToOverlap k)).symm
  let c : KernelFork (twistingCompatibilityMap k n) :=
    KernelFork.ofι (kernel.ι (twistingCompatibilityMap k n))
      (kernel.condition (twistingCompatibilityMap k n))
  have hc : IsLimit c := kernelIsKernel (twistingCompatibilityMap k n)
  have hcF : IsLimit (c.map F) := c.mapIsLimit hc F
  let c' : KernelFork h :=
    KernelFork.ofι ((c.map F).ι ≫ e.hom) (by
      rw [Category.assoc, ← hmap]
      exact (c.map F).condition)
  have hc' : IsLimit c' := by
    apply KernelFork.isLimitOfIsLimitOfIff hcF h e
    intro W φ
    constructor
    · intro hφ
      rw [hmap] at hφ
      simpa only [Category.assoc] using hφ
    · intro hφ
      rw [hmap]
      simpa only [Category.assoc] using hφ
  have hi : IsIso (c'.ι ≫ biprod.snd) :=
    kernelFork_snd_isIso_of_isLimit_desc_neg (F.map f) (F.map g) c' hc'
  have heq : c'.ι ≫ biprod.snd =
      F.map (kernel.ι (twistingCompatibilityMap k n) ≫ biprod.snd) := by
    change ((c.map F).ι ≫ e.hom) ≫ biprod.snd =
      F.map (kernel.ι (twistingCompatibilityMap k n) ≫ biprod.snd)
    rw [Category.assoc, Functor.mapBiprod_hom]
    simp only [biprod.lift_snd]
    rfl
  change IsIso (F.map (kernel.ι (twistingCompatibilityMap k n) ≫ biprod.snd))
  rw [← heq]
  exact hi

/-- The restriction of `O(n)` to the second standard affine chart is the
trivial rank-one module sheaf. -/
noncomputable def x1TwistingSheafIso
    (k : Type u) [CommRing k] (n : ℤ) :
    (twistingSheaf k n).restrict (x1BasicOpen k).ι ≅ x1TrivialModule k := by
  let F := Scheme.Modules.restrictFunctor (x1BasicOpen k).ι
  letI : IsIso (F.map (twistingSheafToX1 k n)) := by
    dsimp [F]
    exact x1Restrict_twistingSheafToX1_isIso k n
  change F.obj (twistingSheaf k n) ≅ x1TrivialModule k
  exact
    asIso (F.map (twistingSheafToX1 k n)) ≪≫
      (Scheme.Modules.restrictFunctorAdjCounitIso (x1BasicOpen k).ι).app
        (x1TrivialModule k)

end

end RiemannRoch.ProjectiveLine
