/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.TwistingSheafTensorIso

/-!
# Duality for twisting sheaves

This file packages the expected duality formula for twisting sheaves on the
projective line.

The project-local sheafified tensor product is not registered as a monoidal
structure on `Scheme.Modules`, so we record duality by its tensor-inverse
content: a chosen module sheaf together with left and right tensor-product
isomorphisms to the structure module.

For every integer `n`, the inverse of `O(n)` is `O(-n)`. The two evaluation
isomorphisms are immediate consequences of the tensor-addition theorem
`O(m) ⊗ O(n) ≅ O(m+n)` and the identification `O(0) ≅ O`.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- Tensor-inverse data for a module sheaf with respect to the project-local
sheafified tensor product. This is the duality notion used until the tensor
product is packaged as a monoidal structure on module sheaves. -/
structure ModuleSheafTensorInverse
    (k : Type u) [CommRing k] (M : ModuleSheaf k) where
  /-- The chosen tensor inverse. -/
  inverse : ModuleSheaf k
  /-- Tensoring on the right by the inverse gives the structure module. -/
  rightIso : moduleSheafTensor k M inverse ≅ structureModule k
  /-- Tensoring on the left by the inverse gives the structure module. -/
  leftIso : moduleSheafTensor k inverse M ≅ structureModule k

/-- The canonical right evaluation isomorphism
`O(n) ⊗ O(-n) ≅ O`. -/
noncomputable def twistingSheafTensorNegIso
    (k : Type u) [CommRing k] (n : ℤ) :
    moduleSheafTensor k (twistingSheaf k n) (twistingSheaf k (-n)) ≅
      structureModule k :=
  twistingSheafTensorIso k n (-n) ≪≫
    eqToIso (congrArg (twistingSheaf k) (add_neg_cancel n)) ≪≫
    twistingSheafZeroIso k

/-- The canonical left evaluation isomorphism
`O(-n) ⊗ O(n) ≅ O`. -/
noncomputable def twistingSheafNegTensorIso
    (k : Type u) [CommRing k] (n : ℤ) :
    moduleSheafTensor k (twistingSheaf k (-n)) (twistingSheaf k n) ≅
      structureModule k :=
  twistingSheafTensorIso k (-n) n ≪≫
    eqToIso (congrArg (twistingSheaf k) (neg_add_cancel n)) ≪≫
    twistingSheafZeroIso k

/-- The twisting sheaf `O(-n)` is a two-sided tensor inverse, hence the
project-local dual, of `O(n)`. -/
noncomputable def twistingSheafTensorInverse
    (k : Type u) [CommRing k] (n : ℤ) :
    ModuleSheafTensorInverse k (twistingSheaf k n) where
  inverse := twistingSheaf k (-n)
  rightIso := twistingSheafTensorNegIso k n
  leftIso := twistingSheafNegTensorIso k n

@[simp]
theorem twistingSheafTensorInverse_inverse
    (k : Type u) [CommRing k] (n : ℤ) :
    (twistingSheafTensorInverse k n).inverse = twistingSheaf k (-n) :=
  rfl

end

end RiemannRoch.ProjectiveLine
