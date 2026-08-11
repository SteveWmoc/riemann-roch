/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import Mathlib.AlgebraicGeometry.Restrict
import RiemannRoch.ProjectiveLine.OverlapTransition

/-!
# The standard two-open cover of the projective line

This file packages the standard opens `D_+(X₀)` and `D_+(X₁)` as Mathlib's
native scheme-theoretic `Scheme.OpenCover`.  The cover is indexed by `Fin 2`,
its component schemes are the corresponding open subschemes, and its component
maps are the canonical open immersions into `P¹`.

The file also records the links from this bundled cover to the affine-line
chart descriptions and to the Laurent-polynomial description of the overlap.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/-- The standard two-open cover `D_+(X₀), D_+(X₁)` of `P¹_k`, packaged as a
scheme-theoretic open cover. Its index type reduces definitionally to `Fin 2`. -/
noncomputable abbrev standardOpenCover (k : Type u) [CommRing k] :
    (scheme k).OpenCover :=
  (scheme k).openCoverOfIsOpenCover (standardBasicOpen k)
    (.mk (iSup_standardBasicOpen_eq_top k))

@[simp]
theorem standardOpenCover_X (k : Type u) [CommRing k] (i : Variable) :
    (standardOpenCover k).X i = (standardBasicOpen k i).toScheme :=
  rfl

@[simp]
theorem standardOpenCover_f (k : Type u) [CommRing k] (i : Variable) :
    (standardOpenCover k).f i = (standardBasicOpen k i).ι :=
  rfl

/-- The range of the `i`th map in the bundled cover is the corresponding
standard homogeneous basic open. -/
@[simp]
theorem standardOpenCover_opensRange (k : Type u) [CommRing k] (i : Variable) :
    ((standardOpenCover k).f i).opensRange = standardBasicOpen k i := by
  rw [standardOpenCover_f, Scheme.Opens.opensRange_ι]

/-- The first component of the standard cover is the affine line. -/
noncomputable def standardOpenCoverX0IsoAffineLine
    (k : Type u) [CommRing k] :
    (standardOpenCover k).X 0 ≅ affineLine k :=
  x0BasicOpenIsoAffineLine k

/-- The second component of the standard cover is the affine line. -/
noncomputable def standardOpenCoverX1IsoAffineLine
    (k : Type u) [CommRing k] :
    (standardOpenCover k).X 1 ≅ affineLine k :=
  x1BasicOpenIsoAffineLine k

/-- The intersection of the two ranges in the bundled cover is the standard
overlap `D_+(X₀) ∩ D_+(X₁)`. -/
@[simp]
theorem standardOpenCover_overlap (k : Type u) [CommRing k] :
    ((standardOpenCover k).f 0).opensRange ⊓
      ((standardOpenCover k).f 1).opensRange = standardOverlap k := by
  simp [standardOverlap]

/-- The overlap of the bundled standard cover is the punctured affine line. -/
noncomputable def standardOpenCoverOverlapIsoPuncturedAffineLine
    (k : Type u) [CommRing k] :
    (((standardOpenCover k).f 0).opensRange ⊓
      ((standardOpenCover k).f 1).opensRange).toScheme ≅ puncturedAffineLine k :=
  (scheme k).isoOfEq (standardOpenCover_overlap k) ≪≫
    standardOverlapIsoPuncturedAffineLine k

end

end RiemannRoch.ProjectiveLine
