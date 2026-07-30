import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import RiemannRoch.ProjectiveLine.BasicOpens

/-!
# Module sheaves and the standard Cech complex

This file records the exact Mathlib interfaces that connect sheaves of modules
on the projective line with abstract sheaf cohomology and with the Cech complex
of the standard two-open cover.

No comparison theorem between the Cech complex and abstract sheaf cohomology is
asserted here. Mathlib currently supplies the two constructions separately.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory

noncomputable section

/-- The abelian category of sheaves of modules over the structure sheaf of
`P^1_k`. -/
abbrev ModuleSheaf (k : Type*) [CommRing k] := (scheme k).Modules

/-- The structure sheaf, regarded as a module over itself. -/
noncomputable def structureSheafModule (k : Type*) [CommRing k] : ModuleSheaf k :=
  SheafOfModules.unit (scheme k).ringCatSheaf

/-- Forget the module structure and retain the underlying sheaf of abelian
groups. This is the input expected by Mathlib's abstract sheaf cohomology. -/
noncomputable def underlyingAbelianSheaf {k : Type*} [CommRing k]
    (M : ModuleSheaf k) :=
  (SheafOfModules.toSheaf (scheme k).ringCatSheaf).obj M

/-- Abstract sheaf cohomology of a module sheaf after forgetting to an abelian
sheaf. -/
abbrev abstractCohomology {k : Type*} [CommRing k]
    (M : ModuleSheaf k) (n : ℕ) :=
  CategoryTheory.Sheaf.H (underlyingAbelianSheaf M) n

/-- The general Cech-complex functor specialized to the standard cover
`D_+(X_0), D_+(X_1)` of `P^1_k`. -/
noncomputable def standardCechComplexFunctor (k : Type*) [CommRing k] :=
  CategoryTheory.cechComplexFunctor (standardBasicOpen k)

/-- The Cech cochain complex of the standard cover with coefficients in a
sheaf of modules, after forgetting to its underlying abelian presheaf. -/
noncomputable def standardCechComplex {k : Type*} [CommRing k]
    (M : ModuleSheaf k) : CochainComplex AddCommGrpCat ℕ :=
  (standardCechComplexFunctor k).obj M.presheaf

end

end RiemannRoch.ProjectiveLine
