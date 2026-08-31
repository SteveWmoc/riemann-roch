/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import Mathlib.Topology.Sheaves.Stalks
import RiemannRoch.ProjectiveLine.TwistingSheafX1Trivialization

/-!
# Detecting isomorphisms on the standard cover

This file packages the local-to-global isomorphism criterion used repeatedly on
`P¹_k`: a morphism of module sheaves is an isomorphism when its restrictions to
both standard affine charts are isomorphisms.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

set_option backward.defeqAttrib.useBackward true in
/-- A morphism of module sheaves that is an isomorphism on both standard charts
is an isomorphism globally. -/
theorem isIso_of_standard_chart_restrictions
    (k : Type u) [CommRing k] {M N : ModuleSheaf k} (φ : M ⟶ N)
    (h0 : IsIso ((Scheme.Modules.restrictFunctor (x0BasicOpen k).ι).map φ))
    (h1 : IsIso ((Scheme.Modules.restrictFunctor (x1BasicOpen k).ι).map φ)) :
    IsIso φ := by
  let ψ :
      (⟨(Scheme.Modules.toPresheaf (scheme k)).obj M,
        by
          rw [Scheme.Modules.toPresheaf_obj]
          exact M.isSheaf⟩ :
          TopCat.Sheaf AddCommGrpCat.{u} (scheme k)) ⟶
      (⟨(Scheme.Modules.toPresheaf (scheme k)).obj N,
        by
          rw [Scheme.Modules.toPresheaf_obj]
          exact N.isSheaf⟩ :
          TopCat.Sheaf AddCommGrpCat.{u} (scheme k)) :=
    ⟨(Scheme.Modules.toPresheaf (scheme k)).map φ⟩
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
        letI : IsIso (e.inv.app M) := by
          change IsIso (e.app M).inv
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
        have hconj :
            e.inv.app M ≫
                ((F ⋙ Scheme.Modules.toPresheaf (x0ChartScheme k) ⋙
                  TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map φ) ≫
                e.hom.app N =
              ((Scheme.Modules.toPresheaf (scheme k) ⋙
                TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
                  ((x0BasicOpen k).ι y)).map φ) := by
          rw [e.hom.naturality φ, ← Category.assoc,
            Iso.inv_hom_id_app, Category.id_comp]
        have hglobal : IsIso
            ((Scheme.Modules.toPresheaf (scheme k) ⋙
              TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
                ((x0BasicOpen k).ι y)).map φ) := by
          rw [← hconj]
          infer_instance
        dsimp only [Functor.comp_obj, Functor.comp_map] at hglobal
        simpa only [ψ, y, Scheme.Opens.ι_apply] using hglobal
      · let y : x1ChartScheme k := ⟨x, hx1⟩
        let F := Scheme.Modules.restrictFunctor (x1BasicOpen k).ι
        let e := Scheme.Modules.restrictStalkNatIso (x1BasicOpen k).ι y
        letI : IsIso (e.inv.app M) := by
          change IsIso (e.app M).inv
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
        have hconj :
            e.inv.app M ≫
                ((F ⋙ Scheme.Modules.toPresheaf (x1ChartScheme k) ⋙
                  TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map φ) ≫
                e.hom.app N =
              ((Scheme.Modules.toPresheaf (scheme k) ⋙
                TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
                  ((x1BasicOpen k).ι y)).map φ) := by
          rw [e.hom.naturality φ, ← Category.assoc,
            Iso.inv_hom_id_app, Category.id_comp]
        have hglobal : IsIso
            ((Scheme.Modules.toPresheaf (scheme k) ⋙
              TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
                ((x1BasicOpen k).ι y)).map φ) := by
          rw [← hconj]
          infer_instance
        dsimp only [Functor.comp_obj, Functor.comp_map] at hglobal
        simpa only [ψ, y, Scheme.Opens.ι_apply] using hglobal
  letI hψ : IsIso ψ :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso ψ
  let eψ := asIso ψ
  haveI : IsIso ψ.hom := by
    change IsIso
      ((TopCat.Sheaf.forget AddCommGrpCat.{u} (scheme k)).map ψ)
    exact ((TopCat.Sheaf.forget AddCommGrpCat.{u} (scheme k)).mapIso eψ).isIso_hom
  haveI : IsIso ((Scheme.Modules.toPresheaf (scheme k)).map φ) := by
    change IsIso ψ.hom
    infer_instance
  exact isIso_of_reflects_iso φ (Scheme.Modules.toPresheaf (scheme k))

end

end RiemannRoch.ProjectiveLine
