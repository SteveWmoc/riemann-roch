import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import RiemannRoch.ProjectiveLine.GradedPolynomialRing

/-!
# Riemann-Roch on the projective line

The first flagship theorem of this project is

`chi(P^1_k, O(n)) = n + 1`

for every field `k` and every integer `n`.

This file is the integration boundary for the projective-line construction,
Mathlib's `Proj` infrastructure, and abstract sheaf cohomology.

Current sequence:

1. Package the standard graded coordinate ring `k[X0, X1]`.
2. Define a stable project-local abbreviation for the resulting `Proj`.
3. Identify the two standard homogeneous basic opens.
4. Prove that they cover `P^1_k`.
5. Identify their coordinate rings and their intersection.
6. Construct the twisting objects needed for `O(n)`.
7. Calculate the resulting two-open Cech complex.
-/

namespace RiemannRoch.ProjectiveLine

end RiemannRoch.ProjectiveLine
