import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Riemann-Roch on the projective line

The first flagship theorem of this project is

`chi(P^1_k, O(n)) = n + 1`

for every field `k` and every integer `n`.

This initial file is intentionally only an import boundary. It verifies that the
project can simultaneously depend on Mathlib's `Proj` infrastructure and its
abstract sheaf-cohomology infrastructure. Precise definitions will be introduced
incrementally as the required APIs are mapped.

Planned first steps:

1. Define the graded polynomial ring used to construct `P^1_k`.
2. Define a stable project-local abbreviation for the resulting `Proj`.
3. Identify the two standard homogeneous basic opens.
4. Prove that they cover `P^1_k`.
5. Identify their coordinate rings and their intersection.
6. Construct the twisting objects needed for `O(n)`.
7. Calculate the resulting two-open Cech complex.
-/

namespace RiemannRoch.ProjectiveLine

end RiemannRoch.ProjectiveLine
