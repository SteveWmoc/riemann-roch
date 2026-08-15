/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import Mathlib.CategoryTheory.Preadditive.Biproducts
import RiemannRoch.ProjectiveLine.SheavesAndCech
import RiemannRoch.ProjectiveLine.TwistingTransition

/-!
# Twisting sheaves on the projective line

This file constructs the twisting sheaf `O(n)` on `P¹_k` from the standard
two-open cover. Both standard charts carry the trivial rank-one module sheaf.
On their overlap, coefficients are identified using the transition factor
`t^(-n)` fixed in `TwistingTransition`.

The global sheaf is realized as the kernel of the difference of the two
restriction maps into the pushforward of the trivial overlap module. This keeps
the construction inside Mathlib's abelian category of sheaves of modules and
leaves the eventual public API independent of the chosen gluing implementation.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

/-- The first standard affine chart as a scheme. -/
abbrev x0ChartScheme (k : Type u) [CommRing k] : Scheme.{u} :=
  (x0BasicOpen k).toScheme

/-- The second standard affine chart as a scheme. -/
abbrev x1ChartScheme (k : Type u) [CommRing k] : Scheme.{u} :=
  (x1BasicOpen k).toScheme

/-- The standard overlap as a scheme. -/
abbrev overlapScheme (k : Type u) [CommRing k] : Scheme.{u} :=
  (standardOverlap k).toScheme

/-- The inclusion of the overlap into the first standard chart. -/
noncomputable abbrev overlapToX0 (k : Type u) [CommRing k] :
    overlapScheme k ⟶ x0ChartScheme k :=
  (scheme k).homOfLE inf_le_left

/-- The inclusion of the overlap into the second standard chart. -/
noncomputable abbrev overlapToX1 (k : Type u) [CommRing k] :
    overlapScheme k ⟶ x1ChartScheme k :=
  (scheme k).homOfLE inf_le_right

/-- The trivial rank-one module sheaf on the first standard chart. -/
noncomputable abbrev x0TrivialModule (k : Type u) [CommRing k] :
    (x0ChartScheme k).Modules :=
  SheafOfModules.unit (x0ChartScheme k).ringCatSheaf

/-- The trivial rank-one module sheaf on the second standard chart. -/
noncomputable abbrev x1TrivialModule (k : Type u) [CommRing k] :
    (x1ChartScheme k).Modules :=
  SheafOfModules.unit (x1ChartScheme k).ringCatSheaf

/-- The trivial rank-one module sheaf on the standard overlap. -/
noncomputable abbrev overlapTrivialModule (k : Type u) [CommRing k] :
    (overlapScheme k).Modules :=
  SheafOfModules.unit (overlapScheme k).ringCatSheaf

/-- A Laurent polynomial, regarded as a global section of the structure sheaf
on the standard overlap via its explicit identification with `Spec k[t,t⁻¹]`. -/
noncomputable def overlapLaurentSection (k : Type u) [CommRing k]
    (f : LaurentPolynomial k) : (overlapTrivialModule k).sections :=
  (standardOverlapIsoPuncturedAffineLine k).hom.appTop
    ((Scheme.ΓSpecIso (.of <| LaurentPolynomial k)).inv f)

/-- Multiplication by the coefficient transition factor `t^(-n)` as an
endomorphism of the trivial rank-one sheaf on the overlap. -/
noncomputable def overlapCoefficientTransitionEnd
    (k : Type u) [CommRing k] (n : ℤ) :
    overlapTrivialModule k ⟶ overlapTrivialModule k :=
  (overlapTrivialModule k).unitHomEquiv.symm
    (overlapLaurentSection k (twistCoefficientTransition k n))

/-- The first trivial chart sheaf, pushed forward to `P¹_k`. -/
noncomputable abbrev x0PushedTrivialModule (k : Type u) [CommRing k] : ModuleSheaf k :=
  (Scheme.Modules.pushforward (x0BasicOpen k).ι).obj (x0TrivialModule k)

/-- The second trivial chart sheaf, pushed forward to `P¹_k`. -/
noncomputable abbrev x1PushedTrivialModule (k : Type u) [CommRing k] : ModuleSheaf k :=
  (Scheme.Modules.pushforward (x1BasicOpen k).ι).obj (x1TrivialModule k)

/-- The trivial overlap sheaf, pushed forward to `P¹_k`. -/
noncomputable abbrev overlapPushedTrivialModule (k : Type u) [CommRing k] : ModuleSheaf k :=
  (Scheme.Modules.pushforward (standardOverlap k).ι).obj (overlapTrivialModule k)

/-- Restrict a section of the first trivial chart module to the overlap, then
push the result forward to `P¹_k`. -/
noncomputable def x0RestrictionToOverlap (k : Type u) [CommRing k] :
    x0PushedTrivialModule k ⟶ overlapPushedTrivialModule k := by
  let r := overlapToX0 k
  let j := (x0BasicOpen k).ι
  let jOverlap := (standardOverlap k).ι
  let O0 := x0TrivialModule k
  let OW := overlapTrivialModule k
  have hcomp : r ≫ j = jOverlap := by
    simp [r, j, jOverlap, standardOverlap]
  exact
    (Scheme.Modules.pushforward j).map
        ((Scheme.Modules.restrictAdjunction r).unit.app O0 ≫
          (Scheme.Modules.pushforward r).map (Scheme.Modules.restrictUnitIso r).hom) ≫
      ((Scheme.Modules.pushforwardComp r j).hom.app OW) ≫
      ((Scheme.Modules.pushforwardCongr hcomp).hom.app OW)

/-- Restrict a section of the second trivial chart module to the overlap, then
push the result forward to `P¹_k`. -/
noncomputable def x1RestrictionToOverlap (k : Type u) [CommRing k] :
    x1PushedTrivialModule k ⟶ overlapPushedTrivialModule k := by
  let r := overlapToX1 k
  let j := (x1BasicOpen k).ι
  let jOverlap := (standardOverlap k).ι
  let O1 := x1TrivialModule k
  let OW := overlapTrivialModule k
  have hcomp : r ≫ j = jOverlap := by
    simp [r, j, jOverlap, standardOverlap]
  exact
    (Scheme.Modules.pushforward j).map
        ((Scheme.Modules.restrictAdjunction r).unit.app O1 ≫
          (Scheme.Modules.pushforward r).map (Scheme.Modules.restrictUnitIso r).hom) ≫
      ((Scheme.Modules.pushforwardComp r j).hom.app OW) ≫
      ((Scheme.Modules.pushforwardCongr hcomp).hom.app OW)

/-- Multiplication by `t^(-n)` on the overlap, pushed forward to `P¹_k`. -/
noncomputable def pushedOverlapCoefficientTransitionEnd
    (k : Type u) [CommRing k] (n : ℤ) :
    overlapPushedTrivialModule k ⟶ overlapPushedTrivialModule k :=
  (Scheme.Modules.pushforward (standardOverlap k).ι).map
    (overlapCoefficientTransitionEnd k n)

/-- The compatibility map whose kernel is `O(n)`. On local coefficients it is
`(a₀, a₁) ↦ t^(-n) a₀ - a₁` on the overlap. -/
noncomputable def twistingCompatibilityMap
    (k : Type u) [CommRing k] (n : ℤ) :
    x0PushedTrivialModule k ⊞ x1PushedTrivialModule k ⟶
      overlapPushedTrivialModule k :=
  biprod.desc
    (x0RestrictionToOverlap k ≫ pushedOverlapCoefficientTransitionEnd k n)
    (-x1RestrictionToOverlap k)

/-- The twisting sheaf `O(n)` on `P¹_k`, constructed by gluing the two trivial
rank-one modules on the standard affine cover with coefficient transition
`t^(-n)`. -/
noncomputable def twistingSheaf (k : Type u) [CommRing k] (n : ℤ) : ModuleSheaf k :=
  kernel (twistingCompatibilityMap k n)

/-- The canonical inclusion of `O(n)` into the pair of pushed-forward local
trivializations. -/
noncomputable abbrev twistingSheafι (k : Type u) [CommRing k] (n : ℤ) :
    twistingSheaf k n ⟶ x0PushedTrivialModule k ⊞ x1PushedTrivialModule k :=
  kernel.ι (twistingCompatibilityMap k n)

@[reassoc (attr := simp)]
theorem twistingSheafι_compatibility
    (k : Type u) [CommRing k] (n : ℤ) :
    twistingSheafι k n ≫ twistingCompatibilityMap k n = 0 :=
  kernel.condition _

end

end RiemannRoch.ProjectiveLine
