/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import RiemannRoch.ProjectiveLine.TwistingSheafCoordinates

/-!
# Standard-chart restrictions of twisting sheaves

This file develops the restriction isomorphisms for the twisting sheaf `O(n)`
on the two standard affine charts of `P¹_k`.

The first chart is now fully trivialized: `x0TwistingSheafIso k n` identifies
the restriction of `O(n)` to `D_+(X₀)` with the trivial rank-one module.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

noncomputable section

universe u v

/-- Restriction along an open immersion is additive. -/
private theorem restrictFunctor_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : (Scheme.Modules.restrictFunctor f).Additive := by
  constructor
  intro M N φ ψ
  apply Scheme.Modules.hom_ext
  intro U
  rfl

/-- The map on sections of an isomorphism of module sheaves is an isomorphism. -/
private theorem modulesHom_app_isIso
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (hf : IsIso f) (U : X.Opens) :
    IsIso (f.app U) := by
  letI : IsIso f := hf
  exact (Scheme.Modules.Hom.isIso_iff_isIso_app).mp hf U

/-- A module-presheaf map induced by equality of opens is an isomorphism. -/
private instance presheafMapEqToHom_isIso
    {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (e : U = V) :
    IsIso (M.presheaf.map (eqToHom e).op) := by
  cases e
  change IsIso (M.presheaf.map (𝟙 (Opposite.op U)))
  rw [M.presheaf.map_id]
  infer_instance

/-- In a preadditive category, the kernel of `(a, b) ↦ f(a) - g(b)` is the
graph of `g⁻¹f` whenever `g` is an isomorphism. In particular its first
projection is an isomorphism. -/
private theorem kernelFork_fst_isIso_of_isLimit_desc_neg
    {C : Type u} [Category.{v} C] [Preadditive C]
    {A B D : C} [HasBinaryBiproduct A B]
    (f : A ⟶ D) (g : B ⟶ D) [IsIso g]
    (c : KernelFork (biprod.desc f (-g))) (hc : IsLimit c) :
    IsIso (c.ι ≫ biprod.fst) := by
  let s : KernelFork (biprod.desc f (-g)) :=
    KernelFork.ofι (biprod.lift (𝟙 A) (f ≫ inv g)) (by
      simp [Category.assoc])
  let l : A ⟶ c.pt := hc.lift s
  have hfg : c.ι ≫ biprod.fst ≫ f = c.ι ≫ biprod.snd ≫ g := by
    have hzero : c.ι ≫ biprod.fst ≫ f - c.ι ≫ biprod.snd ≫ g = 0 := by
      simpa [biprod.desc_eq, sub_eq_add_neg, Category.assoc] using c.condition
    exact sub_eq_zero.mp hzero
  have hsnd : c.ι ≫ biprod.snd = c.ι ≫ biprod.fst ≫ f ≫ inv g := by
    rw [← cancel_mono g]
    simpa [Category.assoc] using hfg.symm
  refine ⟨⟨l, ?_, ?_⟩⟩
  · apply Fork.IsLimit.hom_ext hc
    simp only [Category.assoc, Category.id_comp]
    rw [show l ≫ c.ι = s.ι from hc.fac s WalkingParallelPair.zero]
    apply biprod.hom_ext
    · simp [s, Category.assoc]
    · simpa [s, Category.assoc] using hsnd.symm
  · rw [← Category.assoc, show l ≫ c.ι = s.ι from hc.fac s WalkingParallelPair.zero]
    simp [s]

set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction to the first standard chart preserves the kernel diagram used
to define `O(n)`.

Mathlib's restriction functor for module sheaves is implemented pointwise by
precomposition on opens followed by restriction of scalars. Both operations
preserve limits, although that composite preservation instance is not currently
registered. -/
theorem x0Restrict_preserves_twisting_kernel
    (k : Type u) [CommRing k] (n : ℤ) :
    PreservesLimit (parallelPair (twistingCompatibilityMap k n) 0)
      (Scheme.Modules.restrictFunctor (x0BasicOpen k).ι) := by
  let j := (x0BasicOpen k).ι
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

/-- On an open contained in the range of an open immersion, the unit of the
restriction--pushforward adjunction is an isomorphism on sections. -/
private theorem restrictAdjunction_unit_app_isIso_of_le_range
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    IsIso (((Scheme.Modules.restrictAdjunction f).unit.app M).app U) := by
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  have hEq : f ''ᵁ f ⁻¹ᵁ U = U := by
    rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hU]
  have hHom : homOfLE (f.image_preimage_le U) = eqToHom hEq :=
    Subsingleton.elim _ _
  rw [hHom]
  exact presheafMapEqToHom_isIso M hEq

/-- An open of the `X0` chart, pulled back to the `X1` chart, lies in the
standard overlap. -/
private theorem x0_image_preimage_x1_le_overlapRange
    (k : Type u) [CommRing k] (U : (x0ChartScheme k).Opens) :
    (x1BasicOpen k).ι ⁻¹ᵁ ((x0BasicOpen k).ι ''ᵁ U) ≤
      (overlapToX1 k).opensRange := by
  let j0 := (x0BasicOpen k).ι
  let j1 := (x1BasicOpen k).ι
  let r := overlapToX1 k
  let W := j1 ⁻¹ᵁ (j0 ''ᵁ U)
  apply (j1.image_le_image_iff W r.opensRange).mp
  calc
    j1 ''ᵁ W = j1.opensRange ⊓ (j0 ''ᵁ U) :=
      j1.image_preimage_eq_opensRange_inf _
    _ ≤ j1.opensRange ⊓ j0.opensRange :=
      inf_le_inf le_rfl (j0.image_le_opensRange U)
    _ = standardOverlap k := by
      simp [j0, j1, standardOverlap, inf_comm]
    _ = j1 ''ᵁ r.opensRange := by
      have hcomp : r ≫ j1 = (standardOverlap k).ι := by
        simp [r, j1, standardOverlap]
      calc
        standardOverlap k = (r ≫ j1).opensRange := by
          apply Opens.ext
          change (standardOverlap k : Set (scheme k)) = Set.range (r ≫ j1)
          rw [hcomp]
          exact (Scheme.Opens.range_ι (standardOverlap k)).symm
        _ = j1 ''ᵁ r.opensRange := Scheme.Hom.opensRange_comp r j1

set_option backward.isDefEq.respectTransparency.types false in
/-- After restriction to the `X0` chart, the `X1`-to-overlap restriction map
is an isomorphism. Geometrically, every point of `X1` visible inside `X0`
already lies in `X0 ∩ X1`. -/
theorem x0Restrict_x1RestrictionToOverlap_isIso
    (k : Type u) [CommRing k] :
    IsIso ((Scheme.Modules.restrictFunctor (x0BasicOpen k).ι).map
      (x1RestrictionToOverlap k)) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  let j0 := (x0BasicOpen k).ι
  change IsIso ((x1RestrictionToOverlap k).app (j0 ''ᵁ U))
  dsimp [x1RestrictionToOverlap]
  refine IsIso.comp_isIso' ?_ ?_
  · refine IsIso.comp_isIso' ?_ ?_
    · exact restrictAdjunction_unit_app_isIso_of_le_range
        (overlapToX1 k) (x1TrivialModule k)
        ((x1BasicOpen k).ι ⁻¹ᵁ (j0 ''ᵁ U))
        (x0_image_preimage_x1_le_overlapRange k U)
    · exact modulesHom_app_isIso _
        ((Scheme.Modules.pushforward (overlapToX1 k)).mapIso
          (Scheme.Modules.restrictUnitIso (overlapToX1 k))).isIso_hom _
  · refine IsIso.comp_isIso' ?_ ?_
    · exact modulesHom_app_isIso _
        ((Scheme.Modules.pushforwardComp (overlapToX1 k) (x1BasicOpen k).ι).app
          (overlapTrivialModule k)).isIso_hom _
    · exact inferInstance

/-- The canonical `X0` coordinate of `O(n)` becomes an isomorphism after
restriction to the first standard chart. -/
theorem x0Restrict_twistingSheafToX0_isIso
    (k : Type u) [CommRing k] (n : ℤ) :
    IsIso ((Scheme.Modules.restrictFunctor (x0BasicOpen k).ι).map
      (twistingSheafToX0 k n)) := by
  let F := Scheme.Modules.restrictFunctor (x0BasicOpen k).ι
  let A := x0PushedTrivialModule k
  let B := x1PushedTrivialModule k
  let D := overlapPushedTrivialModule k
  let f : A ⟶ D :=
    x0RestrictionToOverlap k ≫ pushedOverlapCoefficientTransitionEnd k n
  let g : B ⟶ D := x1RestrictionToOverlap k
  letI : F.Additive := restrictFunctor_additive (x0BasicOpen k).ι
  letI : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  letI : PreservesBinaryBiproduct A B F :=
    preservesBinaryBiproduct_of_preservesBiproduct F A B
  letI : PreservesLimit (parallelPair (twistingCompatibilityMap k n) 0) F :=
    x0Restrict_preserves_twisting_kernel k n
  letI : IsIso (F.map g) := by
    dsimp [g, F]
    exact x0Restrict_x1RestrictionToOverlap_isIso k
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
  have hi : IsIso (c'.ι ≫ biprod.fst) :=
    kernelFork_fst_isIso_of_isLimit_desc_neg (F.map f) (F.map g) c' hc'
  have heq : c'.ι ≫ biprod.fst =
      F.map (kernel.ι (twistingCompatibilityMap k n) ≫ biprod.fst) := by
    change ((c.map F).ι ≫ e.hom) ≫ biprod.fst =
      F.map (kernel.ι (twistingCompatibilityMap k n) ≫ biprod.fst)
    rw [Category.assoc, Functor.mapBiprod_hom]
    simp only [biprod.lift_fst]
    rfl
  change IsIso (F.map (kernel.ι (twistingCompatibilityMap k n) ≫ biprod.fst))
  rw [← heq]
  exact hi

/-- The restriction of `O(n)` to the first standard affine chart is the
trivial rank-one module sheaf. -/
noncomputable def x0TwistingSheafIso
    (k : Type u) [CommRing k] (n : ℤ) :
    (twistingSheaf k n).restrict (x0BasicOpen k).ι ≅ x0TrivialModule k := by
  let F := Scheme.Modules.restrictFunctor (x0BasicOpen k).ι
  letI : IsIso (F.map (twistingSheafToX0 k n)) := by
    dsimp [F]
    exact x0Restrict_twistingSheafToX0_isIso k n
  change F.obj (twistingSheaf k n) ≅ x0TrivialModule k
  exact
    asIso (F.map (twistingSheafToX0 k n)) ≪≫
      (Scheme.Modules.restrictFunctorAdjCounitIso (x0BasicOpen k).ι).app
        (x0TrivialModule k)

end

end RiemannRoch.ProjectiveLine
