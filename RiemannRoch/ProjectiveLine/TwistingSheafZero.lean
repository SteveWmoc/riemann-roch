/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import Mathlib.Topology.Sheaves.Stalks
import RiemannRoch.ProjectiveLine.TwistingSheafX1Trivialization

/-!
# The untwisted twisting sheaf

This file identifies the twisting sheaf `O(0)` with the structure sheaf of
`P¹_k`.

The comparison morphism is obtained by restricting a structure-sheaf section
to the two standard charts and applying the local-coordinate gluing universal
property of `twistingSheaf`. It is an isomorphism because its restriction to
each member of the standard cover is an isomorphism.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

/-- The structure sheaf, regarded as its own rank-one module sheaf. -/
noncomputable abbrev structureModule (k : Type u) [CommRing k] : ModuleSheaf k :=
  SheafOfModules.unit (scheme k).ringCatSheaf

/-- The canonical structure-module map to the first pushed-forward
trivial chart module. -/
noncomputable def structureModuleToX0
    (k : Type u) [CommRing k] :
    structureModule k ⟶ x0PushedTrivialModule k :=
  let j := (x0BasicOpen k).ι
  (Scheme.Modules.restrictAdjunction j).unit.app (structureModule k) ≫
    (Scheme.Modules.pushforward j).map
      (Scheme.Modules.restrictUnitIso j).hom

/-- The canonical structure-module map to the second pushed-forward
trivial chart module. -/
noncomputable def structureModuleToX1
    (k : Type u) [CommRing k] :
    structureModule k ⟶ x1PushedTrivialModule k :=
  let j := (x1BasicOpen k).ι
  (Scheme.Modules.restrictAdjunction j).unit.app (structureModule k) ≫
    (Scheme.Modules.pushforward j).map
      (Scheme.Modules.restrictUnitIso j).hom

/-- Restricting the canonical map from a structure module to the
pushforward of the restricted structure module gives an isomorphism. -/
private theorem restrict_structureModuleToPushedUnit_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    IsIso ((Scheme.Modules.restrictFunctor f).map
      ((Scheme.Modules.restrictAdjunction f).unit.app
          (SheafOfModules.unit Y.ringCatSheaf) ≫
        (Scheme.Modules.pushforward f).map
          (Scheme.Modules.restrictUnitIso f).hom)) := by
  let F := Scheme.Modules.restrictFunctor f
  let O := SheafOfModules.unit Y.ringCatSheaf
  let e := (Scheme.Modules.restrictFunctorAdjCounitIso f).app (F.obj O)
  have hunit :
      F.map ((Scheme.Modules.restrictAdjunction f).unit.app O) = e.inv := by
    apply e.comp_hom_eq_id.mp
    change F.map ((Scheme.Modules.restrictAdjunction f).unit.app O) ≫
      (Scheme.Modules.restrictAdjunction f).counit.app (F.obj O) = 𝟙 _
    exact (Scheme.Modules.restrictAdjunction f).left_triangle_components O
  haveI : IsIso
      (F.map ((Scheme.Modules.restrictAdjunction f).unit.app O)) := by
    rw [hunit]
    infer_instance
  change IsIso (F.map
    ((Scheme.Modules.restrictAdjunction f).unit.app O ≫
      (Scheme.Modules.pushforward f).map
        (Scheme.Modules.restrictUnitIso f).hom))
  rw [Functor.map_comp]
  exact
    ((asIso (F.map ((Scheme.Modules.restrictAdjunction f).unit.app O))) ≪≫
      F.mapIso ((Scheme.Modules.pushforward f).mapIso
        (Scheme.Modules.restrictUnitIso f))).isIso_hom

/-- The first canonical structure-module chart map is locally an isomorphism. -/
theorem x0Restrict_structureModuleToX0_isIso
    (k : Type u) [CommRing k] :
    IsIso ((Scheme.Modules.restrictFunctor (x0BasicOpen k).ι).map
      (structureModuleToX0 k)) := by
  change IsIso ((Scheme.Modules.restrictFunctor (x0BasicOpen k).ι).map
    ((Scheme.Modules.restrictAdjunction (x0BasicOpen k).ι).unit.app
        (SheafOfModules.unit (scheme k).ringCatSheaf) ≫
      (Scheme.Modules.pushforward (x0BasicOpen k).ι).map
        (Scheme.Modules.restrictUnitIso (x0BasicOpen k).ι).hom))
  exact restrict_structureModuleToPushedUnit_isIso (x0BasicOpen k).ι

/-- The second canonical structure-module chart map is locally an isomorphism. -/
theorem x1Restrict_structureModuleToX1_isIso
    (k : Type u) [CommRing k] :
    IsIso ((Scheme.Modules.restrictFunctor (x1BasicOpen k).ι).map
      (structureModuleToX1 k)) := by
  change IsIso ((Scheme.Modules.restrictFunctor (x1BasicOpen k).ι).map
    ((Scheme.Modules.restrictAdjunction (x1BasicOpen k).ι).unit.app
        (SheafOfModules.unit (scheme k).ringCatSheaf) ≫
      (Scheme.Modules.pushforward (x1BasicOpen k).ι).map
        (Scheme.Modules.restrictUnitIso (x1BasicOpen k).ι).hom))
  exact restrict_structureModuleToPushedUnit_isIso (x1BasicOpen k).ι

theorem structureModuleToX0_app_one
    (k : Type u) [CommRing k] (U : (scheme k).Opens) :
    (structureModuleToX0 k).app U (1 : Γ(scheme k, U)) =
      (1 : Γ(x0ChartScheme k, (x0BasicOpen k).ι ⁻¹ᵁ U)) := by
  change (((x0BasicOpen k).ι.appIso _).hom
    ((scheme k).presheaf.map _ 1)) = 1
  simp

theorem structureModuleToX1_app_one
    (k : Type u) [CommRing k] (U : (scheme k).Opens) :
    (structureModuleToX1 k).app U (1 : Γ(scheme k, U)) =
      (1 : Γ(x1ChartScheme k, (x1BasicOpen k).ι ⁻¹ᵁ U)) := by
  change (((x1BasicOpen k).ι.appIso _).hom
    ((scheme k).presheaf.map _ 1)) = 1
  simp

theorem x0RestrictionToOverlap_app_one
    (k : Type u) [CommRing k] (U : (scheme k).Opens) :
    (x0RestrictionToOverlap k).app U
        (1 : Γ(x0ChartScheme k, (x0BasicOpen k).ι ⁻¹ᵁ U)) =
      (1 : Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ U)) := by
  change (overlapScheme k).presheaf.map _
      (((overlapToX0 k).appIso _).hom
        ((x0ChartScheme k).presheaf.map _ 1)) = 1
  simp

theorem x1RestrictionToOverlap_app_one
    (k : Type u) [CommRing k] (U : (scheme k).Opens) :
    (x1RestrictionToOverlap k).app U
        (1 : Γ(x1ChartScheme k, (x1BasicOpen k).ι ⁻¹ᵁ U)) =
      (1 : Γ(overlapScheme k, (standardOverlap k).ι ⁻¹ᵁ U)) := by
  change (overlapScheme k).presheaf.map _
      (((overlapToX1 k).appIso _).hom
        ((x1ChartScheme k).presheaf.map _ 1)) = 1
  simp

/-- Multiplication by the degree-zero transition factor is the identity on the
trivial overlap module. -/
@[simp]
theorem overlapCoefficientTransitionEnd_zero
    (k : Type u) [CommRing k] :
    overlapCoefficientTransitionEnd k 0 = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change Γ(overlapScheme k, U) at x
  change x * (overlapScheme k).presheaf.map
      (homOfLE (show U ≤ ⊤ from le_top)).op
      (overlapLaurentTopSection k (twistCoefficientTransition k 0)) = x
  simp [overlapLaurentTopSection]

/-- The pushed-forward degree-zero coefficient transition is the identity. -/
@[simp]
theorem pushedOverlapCoefficientTransitionEnd_zero
    (k : Type u) [CommRing k] :
    pushedOverlapCoefficientTransitionEnd k 0 = 𝟙 _ := by
  simp [pushedOverlapCoefficientTransitionEnd]

/-- The two restrictions of the structure module agree on the standard
overlap. -/
theorem structureModule_chart_compatibility
    (k : Type u) [CommRing k] :
    structureModuleToX0 k ≫ x0RestrictionToOverlap k =
      structureModuleToX1 k ≫ x1RestrictionToOverlap k := by
  apply (overlapPushedTrivialModule k).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  change ((structureModuleToX0 k ≫ x0RestrictionToOverlap k).app U.unop)
      (1 : Γ(scheme k, U.unop)) =
    ((structureModuleToX1 k ≫ x1RestrictionToOverlap k).app U.unop)
      (1 : Γ(scheme k, U.unop))
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
  change (x0RestrictionToOverlap k).app U.unop
      ((structureModuleToX0 k).app U.unop
        (1 : Γ(scheme k, U.unop))) =
    (x1RestrictionToOverlap k).app U.unop
      ((structureModuleToX1 k).app U.unop
        (1 : Γ(scheme k, U.unop)))
  rw [structureModuleToX0_app_one k U.unop,
    structureModuleToX1_app_one k U.unop,
    x0RestrictionToOverlap_app_one k U.unop,
    x1RestrictionToOverlap_app_one k U.unop]

/-- The canonical comparison from the structure module to `O(0)`. -/
noncomputable def structureModuleToTwistingSheafZero
    (k : Type u) [CommRing k] :
    structureModule k ⟶ twistingSheaf k 0 :=
  twistingSheafLift k 0 (structureModuleToX0 k) (structureModuleToX1 k) (by
    simpa using structureModule_chart_compatibility k)

@[reassoc]
theorem structureModuleToTwistingSheafZero_toX0
    (k : Type u) [CommRing k] :
    structureModuleToTwistingSheafZero k ≫ twistingSheafToX0 k 0 =
      structureModuleToX0 k := by
  apply twistingSheafLift_toX0

@[reassoc]
theorem structureModuleToTwistingSheafZero_toX1
    (k : Type u) [CommRing k] :
    structureModuleToTwistingSheafZero k ≫ twistingSheafToX1 k 0 =
      structureModuleToX1 k := by
  apply twistingSheafLift_toX1

/-- The comparison from the structure module to `O(0)` is an
isomorphism on the first standard chart. -/
theorem x0Restrict_structureModuleToTwistingSheafZero_isIso
    (k : Type u) [CommRing k] :
    IsIso ((Scheme.Modules.restrictFunctor (x0BasicOpen k).ι).map
      (structureModuleToTwistingSheafZero k)) := by
  let F := Scheme.Modules.restrictFunctor (x0BasicOpen k).ι
  letI : IsIso (F.map (twistingSheafToX0 k 0)) :=
    x0Restrict_twistingSheafToX0_isIso k 0
  letI : IsIso (F.map (structureModuleToX0 k)) :=
    x0Restrict_structureModuleToX0_isIso k
  have hfac :
      F.map (structureModuleToTwistingSheafZero k) ≫
          F.map (twistingSheafToX0 k 0) =
        F.map (structureModuleToX0 k) := by
    rw [← F.map_comp, structureModuleToTwistingSheafZero_toX0]
  exact IsIso.of_isIso_fac_right hfac

/-- The comparison from the structure module to `O(0)` is an
isomorphism on the second standard chart. -/
theorem x1Restrict_structureModuleToTwistingSheafZero_isIso
    (k : Type u) [CommRing k] :
    IsIso ((Scheme.Modules.restrictFunctor (x1BasicOpen k).ι).map
      (structureModuleToTwistingSheafZero k)) := by
  let F := Scheme.Modules.restrictFunctor (x1BasicOpen k).ι
  letI : IsIso (F.map (twistingSheafToX1 k 0)) :=
    x1Restrict_twistingSheafToX1_isIso k 0
  letI : IsIso (F.map (structureModuleToX1 k)) :=
    x1Restrict_structureModuleToX1_isIso k
  have hfac :
      F.map (structureModuleToTwistingSheafZero k) ≫
          F.map (twistingSheafToX1 k 0) =
        F.map (structureModuleToX1 k) := by
    rw [← F.map_comp, structureModuleToTwistingSheafZero_toX1]
  exact IsIso.of_isIso_fac_right hfac

/-- A morphism of module sheaves that is an isomorphism on both
standard charts is an isomorphism globally. -/
private theorem isIso_of_standard_chart_restrictions
    (k : Type u) [CommRing k] {M N : ModuleSheaf k} (φ : M ⟶ N)
    (h0 : IsIso ((Scheme.Modules.restrictFunctor (x0BasicOpen k).ι).map φ))
    (h1 : IsIso ((Scheme.Modules.restrictFunctor (x1BasicOpen k).ι).map φ)) :
    IsIso φ := by
  let ψ :
      (⟨M.presheaf, M.isSheaf⟩ :
        TopCat.Sheaf AddCommGrpCat.{u} (scheme k)) ⟶
      (⟨N.presheaf, N.isSheaf⟩ :
        TopCat.Sheaf AddCommGrpCat.{u} (scheme k)) :=
    ⟨φ.mapPresheaf⟩
  haveI hstalk : ∀ x : scheme k,
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ψ.hom) :=
    fun x => by
      have hx : x ∈ x0BasicOpen k ∨ x ∈ x1BasicOpen k := by
        have hx' : x ∈ x0BasicOpen k ⊔ x1BasicOpen k := by
          rw [x0BasicOpen_sup_x1BasicOpen_eq_top]
          trivial
        simpa only [Opens.mem_sup] using hx'
      rcases hx with hx0 | hx1
      · let y : x0ChartScheme k := ⟨x, hx0⟩
        let F := Scheme.Modules.restrictFunctor (x0BasicOpen k).ι
        let e := Scheme.Modules.restrictStalkNatIso (x0BasicOpen k).ι y
        letI : IsIso (e.hom.app M) := by
          change IsIso (e.app M).hom
          infer_instance
        letI : IsIso (e.hom.app N) := by
          change IsIso (e.app N).hom
          infer_instance
        letI : IsIso (F.map φ) := h0
        haveI : IsIso ((F ⋙ Scheme.Modules.toPresheaf (x0ChartScheme k) ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map φ) := by
          change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
            ((Scheme.Modules.toPresheaf (x0ChartScheme k)).map (F.map φ)))
          infer_instance
        have hglobal : IsIso
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
              ((x0BasicOpen k).ι y)).map
                ((Scheme.Modules.toPresheaf (scheme k)).map φ)) :=
          IsIso.of_isIso_fac_left (e.hom.naturality φ).symm
        simpa only [ψ, y, Scheme.Opens.ι_apply,
          Scheme.Modules.toPresheaf_map, Scheme.Modules.toPresheaf_obj] using hglobal
      · let y : x1ChartScheme k := ⟨x, hx1⟩
        let F := Scheme.Modules.restrictFunctor (x1BasicOpen k).ι
        let e := Scheme.Modules.restrictStalkNatIso (x1BasicOpen k).ι y
        letI : IsIso (e.hom.app M) := by
          change IsIso (e.app M).hom
          infer_instance
        letI : IsIso (e.hom.app N) := by
          change IsIso (e.app N).hom
          infer_instance
        letI : IsIso (F.map φ) := h1
        haveI : IsIso ((F ⋙ Scheme.Modules.toPresheaf (x1ChartScheme k) ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map φ) := by
          change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
            ((Scheme.Modules.toPresheaf (x1ChartScheme k)).map (F.map φ)))
          infer_instance
        have hglobal : IsIso
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
              ((x1BasicOpen k).ι y)).map
                ((Scheme.Modules.toPresheaf (scheme k)).map φ)) :=
          IsIso.of_isIso_fac_left (e.hom.naturality φ).symm
        simpa only [ψ, y, Scheme.Opens.ι_apply,
          Scheme.Modules.toPresheaf_map, Scheme.Modules.toPresheaf_obj] using hglobal
  haveI : IsIso ψ :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso ψ
  haveI : IsIso ψ.hom := by
    change IsIso
      ((TopCat.Sheaf.forget AddCommGrpCat.{u} (scheme k)).map ψ)
    infer_instance
  haveI : IsIso ((Scheme.Modules.toPresheaf (scheme k)).map φ) := by
    simpa only [ψ, Scheme.Modules.toPresheaf_map] using
      (inferInstance : IsIso ψ.hom)
  exact isIso_of_reflects_iso φ (Scheme.Modules.toPresheaf (scheme k))

/-- The canonical comparison from the structure module to `O(0)` is an
isomorphism. -/
theorem structureModuleToTwistingSheafZero_isIso
    (k : Type u) [CommRing k] :
    IsIso (structureModuleToTwistingSheafZero k) :=
  isIso_of_standard_chart_restrictions k
    (structureModuleToTwistingSheafZero k)
    (x0Restrict_structureModuleToTwistingSheafZero_isIso k)
    (x1Restrict_structureModuleToTwistingSheafZero_isIso k)

end

end RiemannRoch.ProjectiveLine
