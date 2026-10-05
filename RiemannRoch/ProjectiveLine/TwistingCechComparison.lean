/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.TwistingCechCoordinates
import RiemannRoch.ProjectiveLine.TwistingSheafX1Trivialization

/-!
# Comparison of the twisting-sheaf Cech complexes

This file compares the normalized standard-cover Cech complex of `O(n)` with
the explicit polynomial/Laurent coordinate complex.

The degree-zero coordinates use the chosen trivializations on the two standard
affine charts. On the overlap we use the `X₁` frame, but express its coefficient
in the `X₀` Laurent coordinate `t = X₁ / X₀`. With this convention the two
restriction maps become

```text
p(t) |-> p(t) t^(-n)
q(u) |-> q(t^-1),
```

which is exactly the differential packaged in `TwistingCechCoordinates`.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace ZeroObject

noncomputable section

universe u

/-- Evaluate an isomorphism of module sheaves on one open set. -/
private noncomputable def modulesIsoApp
    {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Γ(M, U) ≅ Γ(N, U) :=
  asIso (e.hom.app U)

/-- Sections over an ambient open are the sections over the top open after
restriction to the corresponding open subscheme. -/
private noncomputable def sectionsRestrictTopIso
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Γ(M, U) ≅ Γ(M.restrict U.ι, ⊤) := by
  change Γ(M, U) ≅ Γ(M, U.ι ''ᵁ ⊤)
  exact M.presheaf.mapIso (eqToIso U.ι_image_top).op

/-- A scheme isomorphism induces the contravariant isomorphism on global
sections. -/
private noncomputable def schemeIsoAppTop
    {X Y : Scheme.{u}} (e : X ≅ Y) : Γ(Y, ⊤) ≅ Γ(X, ⊤) where
  hom := e.hom.appTop
  inv := e.inv.appTop
  hom_inv_id := by
    rw [← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop]
  inv_hom_id := by
    rw [← Scheme.Hom.comp_appTop, e.hom_inv_id, Scheme.Hom.id_appTop]

/-- Global sections of the trivial module on the first standard chart are
polynomials in the `X₀`-chart coordinate. -/
private noncomputable def x0TrivialTopPolynomialIso
    (k : Type u) [CommRing k] :
    Γ(x0TrivialModule k, ⊤) ≅ AddCommGrpCat.of (Polynomial k) := by
  change
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj Γ(x0ChartScheme k, ⊤) ≅
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj (.of <| Polynomial k)
  exact (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso <|
    (schemeIsoAppTop (x0BasicOpenIsoAffineLine k)).symm ≪≫
      Scheme.ΓSpecIso (.of <| Polynomial k)

/-- Ring coordinates on global sections of the second standard chart. -/
private noncomputable def x1TrivialTopPolynomialRingIso
    (k : Type u) [CommRing k] :
    Γ(x1ChartScheme k, ⊤) ≅ CommRingCat.of (Polynomial k) :=
  (schemeIsoAppTop (x1BasicOpenIsoSpec k)).symm ≪≫
    Scheme.ΓSpecIso (.of <| standardAway k 1) ≪≫
      ((x1ChartRingEquiv k).symm).toCommRingCatIso

/-- Global sections of the trivial module on the second standard chart are
polynomials in the `X₁`-chart coordinate. -/
private noncomputable def x1TrivialTopPolynomialIso
    (k : Type u) [CommRing k] :
    Γ(x1TrivialModule k, ⊤) ≅ AddCommGrpCat.of (Polynomial k) := by
  change
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj Γ(x1ChartScheme k, ⊤) ≅
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj (.of <| Polynomial k)
  exact (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso
    (x1TrivialTopPolynomialRingIso k)

/-- Ring coordinates on global sections of the standard overlap. -/
private noncomputable def overlapTrivialTopLaurentRingIso
    (k : Type u) [CommRing k] :
    Γ(overlapScheme k, ⊤) ≅ CommRingCat.of (LaurentPolynomial k) :=
  (schemeIsoAppTop (standardOverlapIsoSpec k)).symm ≪≫
    Scheme.ΓSpecIso (.of <| overlapAway k) ≪≫
      ((laurentPolynomialEquivOverlapAway k).symm).toCommRingCatIso

/-- Global sections of the trivial module on the overlap are Laurent
polynomials in the `X₀`-chart coordinate. -/
private noncomputable def overlapTrivialTopLaurentIso
    (k : Type u) [CommRing k] :
    Γ(overlapTrivialModule k, ⊤) ≅ AddCommGrpCat.of (LaurentPolynomial k) := by
  change
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj Γ(overlapScheme k, ⊤) ≅
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj (.of <| LaurentPolynomial k)
  exact (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso
    (overlapTrivialTopLaurentRingIso k)

/-- The overlap inclusion factors through the second standard chart. -/
private theorem overlapToX1_comp_x1BasicOpen_ι
    (k : Type u) [CommRing k] :
    overlapToX1 k ≫ (x1BasicOpen k).ι = (standardOverlap k).ι := by
  simp [standardOverlap]

/-- On the standard overlap, `O(n)` is trivialized using the `X₁` frame. -/
noncomputable def overlapTwistingSheafIso
    (k : Type u) [CommRing k] (n : ℤ) :
    (twistingSheaf k n).restrict (standardOverlap k).ι ≅
      overlapTrivialModule k :=
  ((Scheme.Modules.restrictFunctorCongr
      (overlapToX1_comp_x1BasicOpen_ι k)).app (twistingSheaf k n)).symm ≪≫
    (Scheme.Modules.restrictFunctorComp
      (overlapToX1 k) (x1BasicOpen k).ι).app (twistingSheaf k n) ≪≫
    (Scheme.Modules.restrictFunctor (overlapToX1 k)).mapIso
      (x1TwistingSheafIso k n) ≪≫
    Scheme.Modules.restrictUnitIso (overlapToX1 k)

/-- Sections of `O(n)` on the first standard chart, in polynomial
coordinates. -/
noncomputable def x0TwistingCechSectionsIso
    (k : Type u) [CommRing k] (n : ℤ) :
    (twistingSheaf k n).presheaf.obj (op (x0BasicOpen k)) ≅
      AddCommGrpCat.of (Polynomial k) :=
  sectionsRestrictTopIso (twistingSheaf k n) (x0BasicOpen k) ≪≫
    modulesIsoApp (x0TwistingSheafIso k n) ⊤ ≪≫
    x0TrivialTopPolynomialIso k

/-- Sections of `O(n)` on the second standard chart, in polynomial
coordinates. -/
noncomputable def x1TwistingCechSectionsIso
    (k : Type u) [CommRing k] (n : ℤ) :
    (twistingSheaf k n).presheaf.obj (op (x1BasicOpen k)) ≅
      AddCommGrpCat.of (Polynomial k) :=
  sectionsRestrictTopIso (twistingSheaf k n) (x1BasicOpen k) ≪≫
    modulesIsoApp (x1TwistingSheafIso k n) ⊤ ≪≫
    x1TrivialTopPolynomialIso k

/-- Sections of `O(n)` on the overlap, expressed in the `X₁` frame and the
`X₀` Laurent coordinate. -/
noncomputable def overlapTwistingCechSectionsIso
    (k : Type u) [CommRing k] (n : ℤ) :
    (twistingSheaf k n).presheaf.obj (op (standardOverlap k)) ≅
      AddCommGrpCat.of (LaurentPolynomial k) :=
  sectionsRestrictTopIso (twistingSheaf k n) (standardOverlap k) ≪≫
    modulesIsoApp (overlapTwistingSheafIso k n) ⊤ ≪≫
    overlapTrivialTopLaurentIso k

/-- Restricting an `X₁`-chart polynomial to the overlap and then
rewriting in the `X₀` Laurent coordinate is Laurent inversion. -/
private theorem x1ChartToOverlap_coordinates
    (k : Type u) [CommRing k] (p : Polynomial k) :
    (laurentPolynomialEquivOverlapAway k).symm
        (x1ToOverlapMap k (x1ChartRingEquiv k p)) =
      twistingCechX1CoordinateRestriction k p := by
  rw [← laurentPolynomialEquivOverlapAwayX1_toLaurent]
  change (overlapLaurentTransition k).symm (Polynomial.toLaurent p) =
    overlapLaurentTransition k (Polynomial.toLaurent p)
  rw [overlapLaurentTransition_eq_invert]
  change (LaurentPolynomial.invert (R := k)).symm (Polynomial.toLaurent p) =
    LaurentPolynomial.invert (Polynomial.toLaurent p)
  rw [LaurentPolynomial.invert_symm]

/-- The second-chart restriction as a ring homomorphism in polynomial/Laurent
coordinates. -/
private noncomputable def x1CoordinateRestrictionRingHom
    (k : Type u) [CommRing k] :
    Polynomial k →+* LaurentPolynomial k :=
  ((laurentPolynomialEquivOverlapAway k).symm).toRingHom.comp
    ((x1ToOverlapMap k).comp (x1ChartRingEquiv k).toRingHom)

@[simp]
private theorem x1CoordinateRestrictionRingHom_apply
    (k : Type u) [CommRing k] (p : Polynomial k) :
    x1CoordinateRestrictionRingHom k p =
      twistingCechX1CoordinateRestriction k p := by
  simpa [x1CoordinateRestrictionRingHom] using x1ChartToOverlap_coordinates k p

/-- The inverse affine presentations intertwine the overlap inclusion with the
localization morphism from the second chart. -/
private theorem standardOverlapIsoSpec_inv_comp_overlapToX1
    (k : Type u) [CommRing k] :
    (standardOverlapIsoSpec k).inv ≫ overlapToX1 k =
      Spec.map (CommRingCat.ofHom (x1ToOverlapMap k)) ≫
        (x1BasicOpenIsoSpec k).inv := by
  rw [← cancel_mono (x1BasicOpenIsoSpec k).hom]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← standardOverlapIsoSpec_hom_SpecMap_x1ToOverlapMap]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

@[reassoc]
private theorem overlapToX1_appTop_affine_coordinates
    (k : Type u) [CommRing k] :
    (overlapToX1 k).appTop ≫ (standardOverlapIsoSpec k).inv.appTop =
      (x1BasicOpenIsoSpec k).inv.appTop ≫
        (Spec.map (CommRingCat.ofHom (x1ToOverlapMap k))).appTop := by
  rw [← Scheme.Hom.comp_appTop, standardOverlapIsoSpec_inv_comp_overlapToX1,
    Scheme.Hom.comp_appTop]

/-- Restriction of functions from the second chart to the overlap, expressed
in the chosen polynomial/Laurent ring coordinates. -/
private theorem x1TrivialTopRestriction_ring_coordinates
    (k : Type u) [CommRing k] :
    (overlapToX1 k).appTop ≫ (overlapTrivialTopLaurentRingIso k).hom =
      (x1TrivialTopPolynomialRingIso k).hom ≫
        CommRingCat.ofHom (x1CoordinateRestrictionRingHom k) := by
  simp only [overlapTrivialTopLaurentRingIso, x1TrivialTopPolynomialRingIso,
    Iso.trans_hom, schemeIsoAppTop, Category.assoc]
  change
    (overlapToX1 k).appTop ≫ (standardOverlapIsoSpec k).inv.appTop ≫
        (Scheme.ΓSpecIso (.of <| overlapAway k)).hom ≫
          ((laurentPolynomialEquivOverlapAway k).symm).toCommRingCatIso.hom =
      (x1BasicOpenIsoSpec k).inv.appTop ≫
        (Scheme.ΓSpecIso (.of <| standardAway k 1)).hom ≫
          ((x1ChartRingEquiv k).symm).toCommRingCatIso.hom ≫
            CommRingCat.ofHom (x1CoordinateRestrictionRingHom k)
  rw [overlapToX1_appTop_affine_coordinates_assoc]
  rw [Scheme.ΓSpecIso_naturality_assoc]
  have htail :
      CommRingCat.ofHom (x1ToOverlapMap k) ≫
          ((laurentPolynomialEquivOverlapAway k).symm).toCommRingCatIso.hom =
        ((x1ChartRingEquiv k).symm).toCommRingCatIso.hom ≫
          CommRingCat.ofHom (x1CoordinateRestrictionRingHom k) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change
      (laurentPolynomialEquivOverlapAway k).symm (x1ToOverlapMap k z) =
        (laurentPolynomialEquivOverlapAway k).symm
          (x1ToOverlapMap k
            (x1ChartRingEquiv k ((x1ChartRingEquiv k).symm z)))
    rw [(x1ChartRingEquiv k).apply_symm_apply]
  rw [htail]

/-- The same second-chart restriction identity after forgetting to additive
groups. -/
private theorem x1TrivialTopRestriction_add_coordinates
    (k : Type u) [CommRing k] :
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          (overlapToX1 k).appTop ≫
        (overlapTrivialTopLaurentIso k).hom =
      (x1TrivialTopPolynomialIso k).hom ≫
        AddCommGrpCat.ofHom (twistingCechX1CoordinateRestriction k) := by
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  change
    F.map (overlapToX1 k).appTop ≫
        F.map (overlapTrivialTopLaurentRingIso k).hom =
      F.map (x1TrivialTopPolynomialRingIso k).hom ≫
        AddCommGrpCat.ofHom (twistingCechX1CoordinateRestriction k)
  have hcoord :
      F.map (CommRingCat.ofHom (x1CoordinateRestrictionRingHom k)) =
        AddCommGrpCat.ofHom (twistingCechX1CoordinateRestriction k) := by
    ext p
    exact x1CoordinateRestrictionRingHom_apply k p
  rw [← hcoord]
  simpa only [Functor.map_comp] using
    congrArg (fun f => F.map f) (x1TrivialTopRestriction_ring_coordinates k)

/-- The native restriction map on the trivial `X₁`-module. -/
private noncomputable def x1TrivialTopRestriction
    (k : Type u) [CommRing k] :
    Γ(x1TrivialModule k, ⊤) ⟶ Γ(overlapTrivialModule k, ⊤) :=
  (x1TrivialModule k).presheaf.map
      (homOfLE (show (overlapToX1 k) ''ᵁ
        (⊤ : (overlapScheme k).Opens) ≤ ⊤ from le_top)).op ≫
    (Scheme.Modules.restrictUnitIso (overlapToX1 k)).hom.app ⊤

/-- The native trivial-module restriction factors as restriction of sections
followed by the canonical identification with the overlap structure sheaf. -/
private theorem x1TrivialTopRestriction_eq
    (k : Type u) [CommRing k] :
    (x1TrivialModule k).presheaf.map
        (homOfLE (show (overlapToX1 k) ''ᵁ
          (⊤ : (overlapScheme k).Opens) ≤ ⊤ from le_top)).op ≫
      (Scheme.Modules.restrictUnitIso (overlapToX1 k)).hom.app ⊤ =
        x1TrivialTopRestriction k := rfl

/-- On elements, the native trivial-module restriction is the usual map on
global functions induced by `overlapToX1`. -/
private theorem x1TrivialTopRestriction_apply
    (k : Type u) [CommRing k] (s : Γ(x1TrivialModule k, ⊤)) :
    x1TrivialTopRestriction k s = (overlapToX1 k).appTop s := by
  let r := overlapToX1 k
  change
    ((x1ChartScheme k).presheaf.map
        (homOfLE (show r ''ᵁ (⊤ : (overlapScheme k).Opens) ≤ ⊤ from le_top)).op ≫
      (r.appIso ⊤).hom) s = r.appTop s
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  change r.appLE ⊤ (r ⁻¹ᵁ ⊤) le_rfl s = r.app ⊤ s
  rw [Scheme.Hom.appLE_eq_app]

/-- The native trivial-module restriction has the expected polynomial/Laurent
coordinate formula. -/
private theorem x1TrivialTopRestriction_coordinates
    (k : Type u) [CommRing k] :
    x1TrivialTopRestriction k ≫ (overlapTrivialTopLaurentIso k).hom =
      (x1TrivialTopPolynomialIso k).hom ≫
        AddCommGrpCat.ofHom (twistingCechX1CoordinateRestriction k) := by
  apply ConcreteCategory.hom_ext
  intro s
  change
    (overlapTrivialTopLaurentIso k).hom (x1TrivialTopRestriction k s) =
      twistingCechX1CoordinateRestriction k ((x1TrivialTopPolynomialIso k).hom s)
  rw [x1TrivialTopRestriction_apply]
  have h := congrArg
    (fun f => (ConcreteCategory.hom f) s)
    (x1TrivialTopRestriction_add_coordinates k)
  exact h

/-- The canonical identification of ambient-open sections with top sections
of the restricted sheaf is the presheaf map induced by `ι(U) = U`. -/
@[simp]
private theorem sectionsRestrictTopIso_hom
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    (sectionsRestrictTopIso M U).hom =
      (M.presheaf.mapIso (eqToIso U.ι_image_top).op).hom := by
  rfl

/-- The inverse canonical identification of top sections of a restricted sheaf
with ambient-open sections is the inverse of the same presheaf `mapIso`. -/
@[simp]
private theorem sectionsRestrictTopIso_inv
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    (sectionsRestrictTopIso M U).inv =
      (M.presheaf.mapIso (eqToIso U.ι_image_top).op).inv := by
  rfl

/-- For the overlap restriction-congruence isomorphism, the inverse of the
component is the component of the inverse natural isomorphism. -/
private theorem overlapRestrictFunctorCongr_app_inv
    (k : Type u) [CommRing k] (M : ModuleSheaf k) :
    ((Scheme.Modules.restrictFunctorCongr
      (overlapToX1_comp_x1BasicOpen_ι k)).app M).inv =
      (Scheme.Modules.restrictFunctorCongr
        (overlapToX1_comp_x1BasicOpen_ι k)).inv.app M := by
  rw [Iso.app_inv]

/-- For restriction along the composite overlap inclusion, the hom of the
component is the component of the hom natural isomorphism. -/
private theorem overlapRestrictFunctorComp_app_hom
    (k : Type u) [CommRing k] (M : ModuleSheaf k) :
    ((Scheme.Modules.restrictFunctorComp
      (overlapToX1 k) (x1BasicOpen k).ι).app M).hom =
      (Scheme.Modules.restrictFunctorComp
        (overlapToX1 k) (x1BasicOpen k).ι).hom.app M := by
  rw [Iso.app_hom]

/-- Applying the module presheaf to the transported overlap inclusion from
`X₁` gives the normalized second-chart Cech restriction map. -/
@[reassoc]
theorem standardNormalizedCechX1Restriction_eq_transport
    (k : Type u) [CommRing k] (M : ModuleSheaf k) :
    M.presheaf.map (eqToHom (x1BasicOpen k).ι_image_top).op ≫
        M.presheaf.map ((x1BasicOpen k).ι.opensFunctor.map
          (homOfLE (show (overlapToX1 k) ''ᵁ
            (⊤ : (overlapScheme k).Opens) ≤
              (⊤ : (x1ChartScheme k).Opens) from le_top))).op ≫
      M.presheaf.map
        (eqToHom (x1BasicOpen_image_overlapToX1_top k).symm).op =
    standardNormalizedCechX1Restriction M := by
  unfold standardNormalizedCechX1Restriction
  rw [← Functor.map_comp, ← Functor.map_comp]
  simp only [← op_comp]
  have h := congrArg (fun f => M.presheaf.map f.op)
    (x1BasicOpen_opensFunctor_map_overlapToX1_top k)
  simpa only [Category.assoc] using h

/-- Naturality of the `X₁` trivialization for restriction to the standard
overlap, followed by the canonical identification of the restricted trivial
module with the overlap structure sheaf.

This is the local-frame square, before identifying sections on an ambient
open with top sections of its open subscheme. -/
@[reassoc]
theorem x1TwistingSheafIso_overlap_naturality
    (k : Type u) [CommRing k] (n : ℤ) :
    ((twistingSheaf k n).restrict (x1BasicOpen k).ι).presheaf.map
        (homOfLE (show (overlapToX1 k) ''ᵁ
          (⊤ : (overlapScheme k).Opens) ≤ ⊤ from le_top)).op ≫
      (x1TwistingSheafIso k n).hom.app ((overlapToX1 k) ''ᵁ ⊤) ≫
        (Scheme.Modules.restrictUnitIso (overlapToX1 k)).hom.app ⊤ =
    (x1TwistingSheafIso k n).hom.app ⊤ ≫
      (x1TrivialModule k).presheaf.map
        (homOfLE (show (overlapToX1 k) ''ᵁ
          (⊤ : (overlapScheme k).Opens) ≤ ⊤ from le_top)).op ≫
        (Scheme.Modules.restrictUnitIso (overlapToX1 k)).hom.app ⊤ := by
  exact (x1TwistingSheafIso k n).hom.mapPresheaf.naturality_assoc
    (homOfLE (show (overlapToX1 k) ''ᵁ
      (⊤ : (overlapScheme k).Opens) ≤ ⊤ from le_top)).op
    ((Scheme.Modules.restrictUnitIso (overlapToX1 k)).hom.app ⊤)

/-- The degree-zero term of the normalized Cech complex of `O(n)` is the
pair of polynomial coordinate rings. -/
noncomputable def twistingCechDegreeZeroIso
    (k : Type u) [CommRing k] (n : ℤ) :
    standardNormalizedCechDegreeZero (twistingSheaf k n) ≅
      twistingCechCoordinateDegreeZero k :=
  biprod.mapIso (x0TwistingCechSectionsIso k n) (x1TwistingCechSectionsIso k n) ≪≫
    AddCommGrpCat.biprodIsoProd _ _

/-- The degree-one term of the normalized Cech complex of `O(n)` is the
Laurent polynomial coordinate ring. -/
noncomputable def twistingCechDegreeOneIso
    (k : Type u) [CommRing k] (n : ℤ) :
    standardNormalizedCechDegreeOne (twistingSheaf k n) ≅
      twistingCechCoordinateDegreeOne k :=
  overlapTwistingCechSectionsIso k n

end

end RiemannRoch.ProjectiveLine
