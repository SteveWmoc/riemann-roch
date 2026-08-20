/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import RiemannRoch.ProjectiveLine.TwistingSheafCoordinates

/-!
# Standard-chart restrictions of twisting sheaves

This file develops the restriction isomorphisms for the twisting sheaf `O(n)`
on the two standard affine charts of `P¹_k`.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

universe u

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
  let X := Opposite.op (j.opensFunctor.obj U.unop)
  letI : PreservesFiniteLimits
      (SheafOfModules.evaluation (scheme k).ringCatSheaf X) :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits
      ((scheme k).ringCatSheaf) X
  change IsLimit
    ((ModuleCat.restrictScalars ((j.appIso U.unop).inv.hom)).mapCone
      ((SheafOfModules.evaluation _ X).mapCone
        (limit.cone (parallelPair (twistingCompatibilityMap k n) 0))))
  exact isLimitOfPreserves _
    (isLimitOfPreserves _ (limit.isLimit (parallelPair (twistingCompatibilityMap k n) 0)))

end

end RiemannRoch.ProjectiveLine
