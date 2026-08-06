/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.X1Dehomogenization

/-!
# The standard charts as affine lines

This file completes the affine-coordinate description of the two standard opens
of the projective line. The ring equivalences

```text
k[t] ≃ (k[X_0, X_1]_(X_i))_0
```

are transported contravariantly through `Spec` and composed with Mathlib's
canonical affine presentations of the homogeneous basic opens.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- The affine line over `k`, represented as the spectrum of `k[t]`. -/
abbrev affineLine (k : Type u) [CommRing k] : Scheme.{u} :=
  Spec (.of <| Polynomial k)

/-- The spectrum of the first standard chart ring is the affine line. -/
noncomputable def x0ChartSpecIsoAffineLine (k : Type u) [CommRing k] :
    Spec (.of <| standardAway k 0) ≅ affineLine k :=
  Scheme.Spec.mapIso (x0ChartRingEquiv k).toCommRingCatIso.op

/-- The spectrum of the second standard chart ring is the affine line. -/
noncomputable def x1ChartSpecIsoAffineLine (k : Type u) [CommRing k] :
    Spec (.of <| standardAway k 1) ≅ affineLine k :=
  Scheme.Spec.mapIso (x1ChartRingEquiv k).toCommRingCatIso.op

/-- The standard open `D_+(X_0)` is isomorphic to the affine line. -/
noncomputable def x0BasicOpenIsoAffineLine (k : Type u) [CommRing k] :
    (x0BasicOpen k).toScheme ≅ affineLine k :=
  x0BasicOpenIsoSpec k ≪≫ x0ChartSpecIsoAffineLine k

/-- The standard open `D_+(X_1)` is isomorphic to the affine line. -/
noncomputable def x1BasicOpenIsoAffineLine (k : Type u) [CommRing k] :
    (x1BasicOpen k).toScheme ≅ affineLine k :=
  x1BasicOpenIsoSpec k ≪≫ x1ChartSpecIsoAffineLine k

end

end RiemannRoch.ProjectiveLine
