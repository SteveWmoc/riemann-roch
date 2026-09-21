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

/-- Global sections of the trivial module on the first standard chart are
polynomials in the `X₀)-chart coordinate. -/
private noncomputable def x0TrivialTopPolynomialIso
    (k : Type u) [CommRing k] :
    Γ(x0TrivialModule k, ⊤) ≅ AddCommGrpCat.of (Polynomial k) := by
  change
    (forget₂ CommRingCat AddCommGrpCat).obj Γ(x0ChartScheme k, ⊤) ≅
      (forget₂ CommRingCat AddCommGrpCat).obj (.of <| Polynomial k)
  exact (forget₂ CommRingCat AddCommGrpCat).mapIso <|
    (asIso (x0BasicOpenIsoAffineLine k).hom.appTop).symm ≪≫
      Scheme.ΓSpecIso (.of <| Polynomial k)

/-- Global sections of the trivial module on the second standard chart are
polynomials in the `X₁)-chart coordinate. -/
private noncomputable def x1TrivialTopPolynomialIso
    (k : Type u) [CommRing k] :
    Γ(x1TrivialModule k, ⊤) ≅ AddCommGrpCat.of (Polynomial k) := by
  change
    (forget₂ CommRingCat AddCommGrpCat).obj Γ(x1ChartScheme k, ⊤) ≅
      (forget₂ CommRingCat AddCommGrpCat).obj (.of <| Polynomial k)
  exact (forget₂ CommRingCat AddCommGrpCat).mapIso <|
    (asIso (x1BasicOpenIsoAffineLine k).hom.appTop).symm ≪≫
      Scheme.ΓSpecIso (.of <| Polynomial k)

/-- Global sections of the trivial module on the overlap are Laurent
polynomials in the `X₀)-chart coordinate. -/
private noncomputable def overlapTrivialTopLaurentIso
    (k : Type u) [CommRing k] :
    Γ(overlapTrivialModule k, ⊤) ≅ AddCommGrpCat.of (LaurentPolynomial k) := by
  change
    (forget₂ CommRingCat AddCommGrpCat).obj Γ(overlapScheme k, ⊤) ≅
      (forget₂ CommRingCat AddCommGrpCat).obj (.of <| LaurentPolynomial k)
  exact (forget₂ CommRingCat AddCommGrpCat).mapIso <|
    (asIso (standardOverlapIsoPuncturedAffineLine k).hom.appTop).symm ≪≫
      Scheme.ΓSpecIso (.of <| LaurentPolynomial k)

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
