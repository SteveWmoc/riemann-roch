/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.Basic
import RiemannRoch.ProjectiveLine.GradedPolynomialRing
import RiemannRoch.ProjectiveLine.BasicOpens
import RiemannRoch.ProjectiveLine.AffineCharts
import RiemannRoch.ProjectiveLine.Dehomogenization
import RiemannRoch.ProjectiveLine.X1Dehomogenization
import RiemannRoch.ProjectiveLine.AffineLineCharts
import RiemannRoch.ProjectiveLine.Overlap
import RiemannRoch.ProjectiveLine.OverlapTransition
import RiemannRoch.ProjectiveLine.StandardCover
import RiemannRoch.ProjectiveLine.SheavesAndCech
import RiemannRoch.ProjectiveLine.TwistingTransition
import RiemannRoch.ProjectiveLine.TwistingSheaf
import RiemannRoch.ProjectiveLine.Target

/-!
# Riemann-Roch in Lean

This is the main import file for the public Riemann-Roch development. It exports
the current projective-line construction, its standard homogeneous opens, the
two affine-line chart isomorphisms, the Laurent-polynomial overlap and its
coordinate transition map, the bundled standard open cover, the module-sheaf
and Cech-complex interfaces used by the planned cohomology calculation, and the
transition-data construction of the twisting sheaves `O(n)`.
-/
