/-
Copyright (c) 2026 Steven Sabean. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Steven Sabean
-/

import RiemannRoch.ProjectiveLine.OverlapTransition

/-!
# Transition factors for twisting sheaves on the projective line

This file begins Phase 2 of the project by fixing the transition-function
convention for the twisting sheaves `O(n)` on the standard cover of `P¹`.

Write `t = X₁ / X₀` on the `X₀` chart. For the standard local frames `e₀` and
`e₁` of `O(n)`, we use the convention

```text
e₁ = t^n e₀.
```

Accordingly, a section written as `a₀ e₀ = a₁ e₁` has coefficient transport

```text
a₁ = t^(-n) a₀.
```

The Laurent monomials introduced here are deliberately kept separate from the
future global sheaf construction. This makes the sign convention explicit and
provides the scalar identities needed to glue the two trivial rank-one module
sheaves in the next step.
-/

namespace RiemannRoch.ProjectiveLine

noncomputable section

universe u

/-- The frame transition factor for `O(n)` on the standard overlap, with the
convention `e₁ = t^n e₀`. -/
noncomputable def twistTransition (k : Type u) [CommRing k] (n : ℤ) :
    LaurentPolynomial k :=
  LaurentPolynomial.T n

@[simp]
theorem twistTransition_zero (k : Type u) [CommRing k] :
    twistTransition k 0 = 1 := by
  simp [twistTransition]

/-- Transition factors add exponents under multiplication. -/
theorem twistTransition_add (k : Type u) [CommRing k] (m n : ℤ) :
    twistTransition k (m + n) =
      twistTransition k m * twistTransition k n := by
  exact LaurentPolynomial.T_add (R := k) m n

@[simp]
theorem twistTransition_neg_mul (k : Type u) [CommRing k] (n : ℤ) :
    twistTransition k (-n) * twistTransition k n = 1 := by
  rw [← twistTransition_add]
  simp

@[simp]
theorem twistTransition_mul_neg (k : Type u) [CommRing k] (n : ℤ) :
    twistTransition k n * twistTransition k (-n) = 1 := by
  rw [← twistTransition_add]
  simp

/-- Every twisting transition factor is a unit on the overlap. -/
theorem twistTransition_isUnit (k : Type u) [CommRing k] (n : ℤ) :
    IsUnit (twistTransition k n) := by
  simpa [twistTransition] using (LaurentPolynomial.isUnit_T (R := k) n)

/-- The factor transporting coefficients from the `X₀` trivialization to the
`X₁` trivialization. If `a₀ e₀ = a₁ e₁`, then
`a₁ = twistCoefficientTransition k n * a₀`. -/
noncomputable def twistCoefficientTransition (k : Type u) [CommRing k] (n : ℤ) :
    LaurentPolynomial k :=
  twistTransition k (-n)

@[simp]
theorem twistCoefficientTransition_zero (k : Type u) [CommRing k] :
    twistCoefficientTransition k 0 = 1 := by
  simp [twistCoefficientTransition]

/-- The frame and coefficient transition factors are mutual inverses. -/
@[simp]
theorem twistCoefficientTransition_mul_twistTransition
    (k : Type u) [CommRing k] (n : ℤ) :
    twistCoefficientTransition k n * twistTransition k n = 1 := by
  simp [twistCoefficientTransition]

/-- The frame and coefficient transition factors are mutual inverses. -/
@[simp]
theorem twistTransition_mul_twistCoefficientTransition
    (k : Type u) [CommRing k] (n : ℤ) :
    twistTransition k n * twistCoefficientTransition k n = 1 := by
  simp [twistCoefficientTransition]

/-- Coefficient transition factors are units on the overlap. -/
theorem twistCoefficientTransition_isUnit
    (k : Type u) [CommRing k] (n : ℤ) :
    IsUnit (twistCoefficientTransition k n) := by
  exact twistTransition_isUnit k (-n)

/-- Coefficient transition factors add exponents under multiplication. -/
theorem twistCoefficientTransition_add
    (k : Type u) [CommRing k] (m n : ℤ) :
    twistCoefficientTransition k (m + n) =
      twistCoefficientTransition k m * twistCoefficientTransition k n := by
  change twistTransition k (-(m + n)) =
    twistTransition k (-m) * twistTransition k (-n)
  rw [neg_add_rev, twistTransition_add, mul_comm]

/-- Changing from the `X₀` Laurent coordinate to the `X₁` Laurent coordinate
negates the exponent of the frame transition factor. -/
@[simp]
theorem overlapLaurentTransition_twistTransition
    (k : Type u) [CommRing k] (n : ℤ) :
    overlapLaurentTransition k (twistTransition k n) =
      twistTransition k (-n) := by
  exact overlapLaurentTransition_T k n

/-- Under the overlap coordinate change, the coefficient transition factor
becomes the frame transition factor. -/
@[simp]
theorem overlapLaurentTransition_twistCoefficientTransition
    (k : Type u) [CommRing k] (n : ℤ) :
    overlapLaurentTransition k (twistCoefficientTransition k n) =
      twistTransition k n := by
  simp [twistCoefficientTransition]

end

end RiemannRoch.ProjectiveLine
