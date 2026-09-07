/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.TensorUnit

/-!
# Restriction and the sheafified tensor product

This file develops the compatibility between restriction to an open subscheme
and the sheafified tensor product used for twisting sheaves.

The first step is to expose the same tensor construction on an arbitrary
scheme. The existing `moduleSheafTensor` on `P¹_k` is definitionally the
special case of this construction.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- The sheafified pointwise tensor product of two module sheaves on an
arbitrary scheme. This is the scheme-general form of `moduleSheafTensor`. -/
noncomputable def schemeModuleSheafTensor
    (X : Scheme.{u}) (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification
    (𝟙 X.ringCatSheaf.obj)).obj
      (modulePresheafTensor X M.val N.val)

/-- The projective-line tensor product is exactly the scheme-general tensor
product specialized to `P¹_k`. -/
theorem moduleSheafTensor_eq_schemeModuleSheafTensor
    (k : Type u) [CommRing k] (M N : ModuleSheaf k) :
    moduleSheafTensor k M N = schemeModuleSheafTensor (scheme k) M N :=
  rfl

end

end RiemannRoch.ProjectiveLine
