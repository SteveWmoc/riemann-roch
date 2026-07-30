import RiemannRoch.ProjectiveLine.GradedPolynomialRing
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The standard homogeneous basic opens of the projective line

This file packages Mathlib's `Proj.basicOpen` API for the standard coordinates
of `Proj k[X0, X1]`.
-/

namespace RiemannRoch.ProjectiveLine

open AlgebraicGeometry

noncomputable section

/-- The projective line over `k`, represented as the `Proj` of the standard
total-degree grading on `k[X0, X1]`. -/
abbrev scheme (k : Type*) [CommRing k] : Scheme :=
  AlgebraicGeometry.Proj (grading k)

/-- The homogeneous coordinate indexed by `i : Fin 2`. -/
abbrev coordinate (k : Type*) [CommRing k] (i : Variable) : CoordinateRing k :=
  MvPolynomial.X i

/-- The standard homogeneous basic open `D_+(X_i)`. -/
abbrev standardBasicOpen (k : Type*) [CommRing k] (i : Variable) :
    (scheme k).Opens :=
  AlgebraicGeometry.Proj.basicOpen (grading k) (coordinate k i)

/-- The standard open `D_+(X_0)`. -/
abbrev x0BasicOpen (k : Type*) [CommRing k] : (scheme k).Opens :=
  standardBasicOpen k 0

/-- The standard open `D_+(X_1)`. -/
abbrev x1BasicOpen (k : Type*) [CommRing k] : (scheme k).Opens :=
  standardBasicOpen k 1

lemma coordinate_mem_grading_one (k : Type*) [CommRing k] (i : Variable) :
    coordinate k i ∈ grading k 1 :=
  MvPolynomial.isHomogeneous_X k i

/-- The two homogeneous coordinates generate the coordinate ring as an algebra
over its degree-zero part. -/
lemma adjoin_coordinates_eq_top (k : Type*) [CommRing k] :
    Algebra.adjoin (grading k 0) (Set.range (coordinate k)) = ⊤ := by
  let S := Algebra.adjoin (grading k 0) (Set.range (coordinate k))
  change S = ⊤
  refine top_unique fun p hp => ?_
  clear hp
  induction p using MvPolynomial.induction_on with
  | C r =>
      exact S.algebraMap_mem ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C Variable r⟩
  | add p q hp hq =>
      exact S.add_mem hp hq
  | mul_X p i hp =>
      exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self i))

/-- The two standard homogeneous basic opens cover the projective line. -/
theorem iSup_standardBasicOpen_eq_top (k : Type*) [CommRing k] :
    ⨆ i : Variable, standardBasicOpen k i = ⊤ := by
  apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top' (grading k) (coordinate k)
  · intro i
    exact ⟨1, coordinate_mem_grading_one k i⟩
  · exact adjoin_coordinates_eq_top k

/-- Binary form of the standard-cover theorem. -/
theorem x0BasicOpen_sup_x1BasicOpen_eq_top (k : Type*) [CommRing k] :
    x0BasicOpen k ⊔ x1BasicOpen k = ⊤ := by
  rw [← iSup_standardBasicOpen_eq_top k]
  apply le_antisymm
  · exact sup_le (le_iSup (standardBasicOpen k) 0) (le_iSup (standardBasicOpen k) 1)
  · refine iSup_le ?_
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j0 => Fin.elim0 j0) j) i
    · exact le_sup_left
    · exact le_sup_right

end

end RiemannRoch.ProjectiveLine
