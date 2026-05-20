/-
  RadialPolynomial.lean — SLICE-OL-05 + SLICE-OL-06

  Defines the rational radial distortion factor R (OpenLensIO §4.1 Eq 17)
  and the denominator-nonzero domain predicate.

  AMB-OL-007 resolution: denominatorNonzero is an explicit precondition,
  not a derived invariant. The caller supplies evidence that the denominator
  is nonzero at the specific point r.

  Naming: k1,k3,k5 are numerator terms; k2,k4,k6 are denominator terms
  (alternating per §4.1 Eq 17). Not the DistortionConversion.lean convention.
-/

import LensSemantics

/-─────────────────────────────────────────────────────────────────────────────
  denominatorNonzero

  Per-point domain predicate for the radial rational polynomial.
  The denominator of R at radius r is 1 + k2·r² + k4·r⁴ + k6·r⁶.
  Nonzero is a caller obligation (AMB-OL-007); this predicate names it.
─────────────────────────────────────────────────────────────────────────────-/

def denominatorNonzero (k : RadialCoefficients) (r : ℝ) : Prop :=
  1 + k.k2 * r ^ 2 + k.k4 * r ^ 4 + k.k6 * r ^ 6 ≠ 0

/-─────────────────────────────────────────────────────────────────────────────
  radialTerm

  The rational radial distortion factor R(r) from §4.1 Eq (17):

    R = (1 + k1·r² + k3·r⁴ + k5·r⁶) / (1 + k2·r² + k4·r⁴ + k6·r⁶)

  Division over ℝ is well-defined because h : denominatorNonzero k r.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def radialTerm (k : RadialCoefficients) (r : ℝ)
    (_ : denominatorNonzero k r) : ℝ :=
  (1 + k.k1 * r ^ 2 + k.k3 * r ^ 4 + k.k5 * r ^ 6) /
  (1 + k.k2 * r ^ 2 + k.k4 * r ^ 4 + k.k6 * r ^ 6)

/-─────────────────────────────────────────────────────────────────────────────
  radial_denominator_nonzero_zero_coeffs

  Canonical domain-safety instance: when all denominator coefficients are zero,
  the denominator is 1, which is nonzero.

  Non-vacuity witness: denominatorNonzero fails for k2 = −1, r = 1 (denominator
  = 1 + (−1)·1 = 0), so the predicate is genuinely constraining.
─────────────────────────────────────────────────────────────────────────────-/

theorem radial_denominator_nonzero_zero_coeffs
    (k : RadialCoefficients) (r : ℝ)
    (hk2 : k.k2 = 0) (hk4 : k.k4 = 0) (hk6 : k.k6 = 0) :
    denominatorNonzero k r := by
  simp [denominatorNonzero, hk2, hk4, hk6]

/-─────────────────────────────────────────────────────────────────────────────
  radial_zero_coefficients_identity

  When all six radial coefficients are zero, R = 1.
  Numerator and denominator both reduce to 1; division yields 1.

  Paper claim: a lens with all-zero k coefficients has no radial distortion
  factor (R = 1), so U reduces to the tangential terms only (see SLICE-OL-08).
─────────────────────────────────────────────────────────────────────────────-/

theorem radial_zero_coefficients_identity
    (k : RadialCoefficients) (r : ℝ)
    (hk1 : k.k1 = 0) (hk2 : k.k2 = 0) (hk3 : k.k3 = 0)
    (hk4 : k.k4 = 0) (hk5 : k.k5 = 0) (hk6 : k.k6 = 0)
    (h : denominatorNonzero k r) :
    radialTerm k r h = 1 := by
  simp only [radialTerm, hk1, hk2, hk3, hk4, hk5, hk6]
  norm_num
