/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.NormalizedCech
import RiemannRoch.ProjectiveLine.TwistingTransition

/-!
# Coordinate Cech complex for twisting sheaves

This file packages the explicit algebraic two-term complex that will model the
normalized standard-cover Cech complex of `O(n)`.

Using the `X₀` affine coordinate `t = X₁ / X₀`, the two chart coefficient
rings are both polynomial rings and the overlap coefficient ring is the Laurent
polynomial ring. The `X₁` coordinate is `t⁻¹`. With the frame convention

```text
e₁ = t^n e₀,
```

coefficient transport from the `X₀` frame to the `X₁` frame is multiplication
by `t^(-n)`. Thus the coordinate differential is

```text
k[t] ⊕ k[u]  ⟶  k[t,t⁻¹]
(p, q)        ↦  t^(-n) p(t) - q(t⁻¹).
```

The comparison with the sheaf-theoretic normalized Cech complex is deliberately
left to a subsequent slice. Keeping this algebraic model separate gives the
kernel and cokernel computations a stable target.
-/

namespace RiemannRoch.ProjectiveLine

open CategoryTheory ZeroObject

noncomputable section

universe u

/-- The `X₀` chart coefficient, restricted to the overlap and transported to
the `X₁` frame. In the `X₀` Laurent coordinate this is
`p(t) * t^(-n)`. -/
noncomputable def twistingCechX0CoordinateRestriction
    (k : Type u) [CommRing k] (n : ℤ) :
    Polynomial k →+ LaurentPolynomial k where
  toFun p := Polynomial.toLaurent p * twistCoefficientTransition k n
  map_zero' := by simp
  map_add' p q := by simp [add_mul]

/-- The `X₁` chart coefficient, restricted to the overlap and rewritten in the
`X₀` Laurent coordinate. This substitutes `u = t⁻¹`. -/
noncomputable def twistingCechX1CoordinateRestriction
    (k : Type u) [CommRing k] :
    Polynomial k →+ LaurentPolynomial k where
  toFun p := overlapLaurentTransition k (Polynomial.toLaurent p)
  map_zero' := by simp
  map_add' p q := by simp

/-- The explicit coordinate differential for the standard-cover Cech complex
of `O(n)`:
`(p, q) ↦ p(t) t^(-n) - q(t⁻¹)`. -/
noncomputable def twistingCechCoordinateDifferentialAddHom
    (k : Type u) [CommRing k] (n : ℤ) :
    (Polynomial k × Polynomial k) →+ LaurentPolynomial k where
  toFun pq :=
    twistingCechX0CoordinateRestriction k n pq.1 -
      twistingCechX1CoordinateRestriction k pq.2
  map_zero' := by simp
  map_add' p q := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Degree zero of the explicit coordinate Cech complex for `O(n)`. -/
noncomputable abbrev twistingCechCoordinateDegreeZero
    (k : Type u) [CommRing k] : AddCommGrpCat :=
  AddCommGrpCat.of (Polynomial k × Polynomial k)

/-- Degree one of the explicit coordinate Cech complex for `O(n)`. -/
noncomputable abbrev twistingCechCoordinateDegreeOne
    (k : Type u) [CommRing k] : AddCommGrpCat :=
  AddCommGrpCat.of (LaurentPolynomial k)

/-- The coordinate Cech differential as a morphism of additive groups. -/
noncomputable def twistingCechCoordinateDifferential
    (k : Type u) [CommRing k] (n : ℤ) :
    twistingCechCoordinateDegreeZero k ⟶ twistingCechCoordinateDegreeOne k :=
  AddCommGrpCat.ofHom (twistingCechCoordinateDifferentialAddHom k n)

@[simp]
theorem twistingCechX0CoordinateRestriction_apply
    (k : Type u) [CommRing k] (n : ℤ) (p : Polynomial k) :
    twistingCechX0CoordinateRestriction k n p =
      Polynomial.toLaurent p * twistCoefficientTransition k n :=
  rfl

@[simp]
theorem twistingCechX1CoordinateRestriction_apply
    (k : Type u) [CommRing k] (p : Polynomial k) :
    twistingCechX1CoordinateRestriction k p =
      overlapLaurentTransition k (Polynomial.toLaurent p) :=
  rfl

@[simp]
theorem twistingCechCoordinateDifferential_apply
    (k : Type u) [CommRing k] (n : ℤ) (p q : Polynomial k) :
    twistingCechCoordinateDifferential k n (p, q) =
      Polynomial.toLaurent p * twistCoefficientTransition k n -
        overlapLaurentTransition k (Polynomial.toLaurent q) :=
  rfl

private noncomputable def twistingCechCoordinateObjects
    (k : Type u) [CommRing k] : ℕ → AddCommGrpCat
  | 0 => twistingCechCoordinateDegreeZero k
  | Nat.succ 0 => twistingCechCoordinateDegreeOne k
  | Nat.succ (Nat.succ _) => 0

private noncomputable def twistingCechCoordinateD
    (k : Type u) [CommRing k] (n : ℤ) :
    (i : ℕ) → twistingCechCoordinateObjects k i ⟶
      twistingCechCoordinateObjects k (i + 1)
  | 0 => twistingCechCoordinateDifferential k n
  | Nat.succ _ => 0

private theorem twistingCechCoordinateD_squared
    (k : Type u) [CommRing k] (n : ℤ) (i : ℕ) :
    twistingCechCoordinateD k n i ≫ twistingCechCoordinateD k n (i + 1) = 0 := by
  cases i with
  | zero => exact HasZeroMorphisms.comp_zero _ _
  | succ i => exact HasZeroMorphisms.zero_comp _ _

/-- The explicit polynomial/Laurent two-term Cech complex for `O(n)`. -/
noncomputable def twistingCechCoordinateComplex
    (k : Type u) [CommRing k] (n : ℤ) :
    CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.of
    (twistingCechCoordinateObjects k)
    (twistingCechCoordinateD k n)
    (twistingCechCoordinateD_squared k n)

@[simp]
theorem twistingCechCoordinateComplex_X_zero
    (k : Type u) [CommRing k] (n : ℤ) :
    (twistingCechCoordinateComplex k n).X 0 =
      twistingCechCoordinateDegreeZero k :=
  rfl

@[simp]
theorem twistingCechCoordinateComplex_X_one
    (k : Type u) [CommRing k] (n : ℤ) :
    (twistingCechCoordinateComplex k n).X 1 =
      twistingCechCoordinateDegreeOne k :=
  rfl

@[simp]
theorem twistingCechCoordinateComplex_X_add_two
    (k : Type u) [CommRing k] (n : ℤ) (i : ℕ) :
    (twistingCechCoordinateComplex k n).X (i + 2) = 0 :=
  rfl

@[simp]
theorem twistingCechCoordinateComplex_d_zero_one
    (k : Type u) [CommRing k] (n : ℤ) :
    (twistingCechCoordinateComplex k n).d 0 1 =
      twistingCechCoordinateDifferential k n := by
  simp [twistingCechCoordinateComplex, CochainComplex.of.d, twistingCechCoordinateD]
  exact Category.comp_id _

end

end RiemannRoch.ProjectiveLine
