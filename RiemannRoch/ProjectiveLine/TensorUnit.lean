/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.TwistingSheafMultiplication

/-!
# Unit laws for the project-local tensor product

The sheaf tensor product used for twisting sheaves is defined by sheafifying
the pointwise tensor product of module presheaves. This file records the
corresponding tensor-unit comparison with the structure module.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

noncomputable section

universe u

/-- Before sheafification, tensoring a module presheaf on the left by the
structure module is canonically the identity. -/
noncomputable def modulePresheafTensorLeftUnitor
    (X : Scheme.{u}) (M : X.PresheafOfModules) :
    modulePresheafTensor X (SheafOfModules.unit X.ringCatSheaf).val M ≅ M :=
  PresheafOfModules.isoMk
    (fun U => ModuleCat.MonoidalCategory.leftUnitor (M.obj U))
    (by
      intro U V f
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro r m
      change M.map f (r • m) = X.ringCatSheaf.obj.map f r • M.map f m
      exact M.map_smul f r m)

end

end RiemannRoch.ProjectiveLine
