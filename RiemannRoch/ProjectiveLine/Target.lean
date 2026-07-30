import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import RiemannRoch.ProjectiveLine.BasicOpens

/-!
# Riemann-Roch on the projective line

The first flagship theorem of this project is

`chi(P^1_k, O(n)) = n + 1`

for every field `k` and every integer `n`.

This file is the integration boundary for the projective-line construction,
Mathlib's `Proj` infrastructure, and abstract sheaf cohomology.

Current sequence:

1. Package the standard graded coordinate ring `k[X0, X1]`.
2. Define `P^1_k` as its `Proj`.
3. Package `D_+(X0)` and `D_+(X1)` and prove that they cover.
4. Identify their coordinate rings and their intersection.
5. Construct the twisting objects needed for `O(n)`.
6. Calculate the resulting two-open Cech complex.
-/

namespace RiemannRoch.ProjectiveLine

end RiemannRoch.ProjectiveLine
