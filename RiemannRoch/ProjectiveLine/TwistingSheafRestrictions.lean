/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

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

This lemma records the exact finite-limit preservation fact needed for the
first local trivialization. -/
theorem x0Restrict_preserves_twisting_kernel
    (k : Type u) [CommRing k] (n : ℤ) :
    PreservesLimit (parallelPair (twistingCompatibilityMap k n) 0)
      (Scheme.Modules.restrictFunctor (x0BasicOpen k).ι) := by
  infer_instance

end

end RiemannRoch.ProjectiveLine
