/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import RiemannRoch.ProjectiveLine.StandardCover

/-!
# Module sheaves and the standard Cech complex

This file records the exact Mathlib interfaces that connect sheaves of modules
on the projective line with abstract sheaf cohomology and with the Cech complex
of the bundled standard two-open cover.

No comparison theorem between the Cech complex and abstract sheaf cohomology is
asserted here. Mathlib currently supplies the two constructions separately.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- The abelian category of sheaves of modules over the structure sheaf of
`P^1_k`. -/
abbrev ModuleSheaf (k : Type u) [CommRing k] := (scheme k).Modules

/-- The structure sheaf, regarded as a module over itself. -/
noncomputable def structureSheafModule (k : Type u) [CommRing k] : ModuleSheaf k :=
  SheafOfModules.unit (scheme k).ringCatSheaf

/-- Forget the module structure and retain the underlying sheaf of abelian
groups. This is the input expected by Mathlib's abstract sheaf cohomology.

The expression `CategoryTheory.Sheaf.H (underlyingAbelianSheaf M) n` additionally
requires the derived-localization and `HasExt` instances appearing in the API of
`Sheaf.H`; we deliberately do not hide those requirements in an abbreviation. -/
noncomputable def underlyingAbelianSheaf {k : Type u} [CommRing k]
    (M : ModuleSheaf k) :=
  (SheafOfModules.toSheaf (scheme k).ringCatSheaf).obj M

/-- The family of open ranges underlying the bundled standard cover. -/
abbrev standardCoverOpens (k : Type u) [CommRing k] :
    Variable → (scheme k).Opens :=
  fun i => ((standardOpenCover k).f i).opensRange

theorem standardCoverOpens_apply (k : Type u) [CommRing k] (i : Variable) :
    standardCoverOpens k i = standardBasicOpen k i :=
  standardOpenCover_opensRange k i

/-- The general Cech-complex functor specialized to the bundled standard cover
`D_+(X_0), D_+(X_1)` of `P^1_k`. -/
noncomputable def standardCechComplexFunctor (k : Type u) [CommRing k] :
    ((scheme k).Opensᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
      CochainComplex AddCommGrpCat.{u} ℕ :=
  CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{u}) (standardCoverOpens k)

/-- The Cech cochain complex of the standard cover with coefficients in a
sheaf of modules, after forgetting to its underlying abelian presheaf. -/
noncomputable def standardCechComplex {k : Type u} [CommRing k]
    (M : ModuleSheaf k) : CochainComplex AddCommGrpCat.{u} ℕ :=
  (standardCechComplexFunctor k).obj M.presheaf

end

end RiemannRoch.ProjectiveLine
