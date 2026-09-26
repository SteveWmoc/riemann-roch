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
  rw [U.ι_image_top]

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
polynomials in the `X₀)-chart coordinate. -/
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
polynomials in the `X₁)-chart coordinate. -/
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
polynomials in the `X₀)-chart coordinate. -/
private noncomputable def overlapTrivialTopLaurentIso
    (k : Type u) [CommRing k] :
    Γ(overlapTrivialModule k, ⊤) ≅ AddCommGrpCat.of (LaurentPolynomial k) := by
  change
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj Γ(overlapScheme k, ⊤) ≅
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj (.of <| LaurentPolynomial k)
  exact (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso
    (overlapTrivialTopLaurentRingIso k)

/-- On the standard overlap, `O(n)` is trivialized using the `X₁` frame. -/
noncomputable def overlapTwistingSheafIso
    (k : Type u) [CommRing k] (n : ℤ) :
    (twistingSheaf k n).restrict (standardOverlap k).ι ≅
      overlapTrivialModule k := by
  let r := overlapToX1 k
  let j := (x1BasicOpen k).ι
  let w := (standardOverlap k).ι
  have hcomp : r ≫ j = w := by
    simp [r, j, w, standardOverlap]
  exact
    ((Scheme.Modules.restrictFunctorCongr hcomp).app (twistingSheaf k n)).symm ≪≫
      (Scheme.Modules.restrictFunctorComp r j).app (twistingSheaf k n) ≪≫
      (Scheme.Modules.restrictFunctor r).mapIso (x1TwistingSheafIso k n) ≪≫
      Scheme.Modules.restrictUnitIso r

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

/-- Restricting an `X₁)-chart polynomial to the overlap and then
rewriting in the `X₀) Laurent coordinate is Laurent inversion. -/
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
