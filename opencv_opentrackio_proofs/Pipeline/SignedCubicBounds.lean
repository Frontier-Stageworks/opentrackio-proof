/-
  Pipeline/SignedCubicBounds.lean

  Pure real-number algebra, independent of Coeffs/RCoeffs/ℂ/SensorPoint: tighter
  sufficient conditions for bounding a cubic f(u) = a*u+b*u^2+c*u^3 (and its
  "divided difference" k(u1,u2) used for Lipschitz bounds) on [0,U], EXPLOITING
  the actual (fixed, known) signs of a,b,c rather than the crude triangle-
  inequality sum of |a|,|b|,|c| used by `Mrad`/`Lrad`
  (`inverse_approximation/InverseApproximation.lean`).

  MOTIVATION (why Mrad/Lrad are conservative for real calibrations): `Mrad θ R
  = |k1|R²+|k2|R⁴+|k3|R⁶` is a valid upper bound via the triangle inequality,
  but it is tight only when k1,k2,k3 have the SAME sign (so the three terms
  reinforce at r=R). Real lens calibrations typically have MIXED signs (e.g.
  TUM fr1: k1=+0.26, k2=-0.95, k3=+1.16) — the middle term partially cancels
  the other two, so the true polynomial value at r=R is much smaller in
  magnitude than the sum of the three terms' individual magnitudes. This file
  proves, for a FIXED, numerically-checkable sign/monotonicity condition on
  a,b,c (not a free hypothesis "for all signs"), that the TIGHT bound is
  simply |f(U)| — the actual signed value at the boundary — instead of the
  sum-of-absolute-coefficients `Mrad`.

  Two independent sufficient conditions are proved, covering every real
  calibration tested in audit/REAL_CALIBRATION_VALIDATION.md:

  - `cubic_tight_pos`/`k_bound_pos`: a GLOBAL discriminant condition
    (b²≤4ac, b²≤3ac respectively) that holds when the polynomial never
    dips negative anywhere (not just on [0,U]) — covers TUM fr1/fr2's
    numerator, where a,c>0 dominate despite b<0.
  - `cubic_tight_neg`/`k_bound_neg`: a LOCAL monotonicity condition
    (a≤0, and a vertex-outside-the-interval inequality) — covers Azure
    Kinect DK's numerator AND denominator, where the large negative b
    makes the polynomial negative throughout the relevant range.

  Neither condition is claimed necessary or universally applicable — each is
  a SUFFICIENT, independently checkable (via `norm_num`/`nlinarith` on the
  concrete numbers) condition, verified per-calibration in
  Pipeline/RealCalibrationExamplesImproved.lean.

  Does not modify InverseApproximation.lean, RationalRadialBounds.lean, or any
  other existing file. No axioms, no `sorry`.
-/

import Mathlib.Tactic

/-─────────────────────────────────────────────────────────────────────────────
  Core quadratic facts — building blocks for both the cubic (boundedness) and
  the "divided difference" (Lipschitz) results below.
─────────────────────────────────────────────────────────────────────────────-/

/-- A quadratic with negative discriminant (and positive leading coefficient)
is nonnegative EVERYWHERE, not just on some interval — proved by completing
the square: `4c·(a+bu+cu²) = (2cu+b)² + (4ac-b²)`. -/
theorem quad_discrim_nonneg (a b c : ℝ) (hc : 0 < c) (hdisc : b ^ 2 ≤ 4 * a * c) (u : ℝ) :
    0 ≤ a + b * u + c * u ^ 2 := by
  nlinarith [sq_nonneg (2 * c * u + b), hc, hdisc]

/-- If a quadratic (c>0) starts at a nonpositive value (a≤0) and is monotonic
non-increasing throughout [0,U] (vertex at or beyond U, i.e. `b+2cU≤0`), it
stays nonpositive throughout [0,U]. -/
theorem quad_mono_nonpos (a b c U : ℝ) (hc : 0 < c) (ha : a ≤ 0) (hmono : b + 2 * c * U ≤ 0)
    (u : ℝ) (hu0 : 0 ≤ u) (huU : u ≤ U) :
    a + b * u + c * u ^ 2 ≤ 0 := by
  nlinarith [mul_nonneg hu0 (by nlinarith : (0:ℝ) ≤ -(b + c * u)), hc]

/-- Under the same monotonicity condition, the quadratic's value at any
interior point is at least its value at the right endpoint U (so U's value is
the tightest available lower bound on the interval). -/
theorem quad_mono_decreasing_lower (a b c S : ℝ) (hc : 0 < c) (hmono : b + 2 * c * S ≤ 0)
    (s : ℝ) (hs0 : 0 ≤ s) (hsS : s ≤ S) :
    a + b * S + c * S ^ 2 ≤ a + b * s + c * s ^ 2 := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ S - s) (by nlinarith : (0:ℝ) ≤ -(b + c * (s + S)))]

/-- A convex quadratic (c>0) never exceeds the larger of its two endpoint
values on [0,S] — the "chord lies above the parabola" fact, needed (unlike
`quad_discrim_nonneg`) with no sign condition on the discriminant at all. -/
theorem quad_chord_upper (a b c S : ℝ) (hc : 0 < c) (hS : 0 ≤ S)
    (s : ℝ) (hs0 : 0 ≤ s) (hsS : s ≤ S) :
    a + b * s + c * s ^ 2 ≤ max a (a + b * S + c * S ^ 2) := by
  rcases lt_or_ge (b + c * S) 0 with hsign | hsign
  · have h1 : a + b * s + c * s ^ 2 ≤ a + (b + c * S) * s := by
      nlinarith [mul_nonneg hs0 (by linarith : (0:ℝ) ≤ S - s)]
    have h2 : a + (b + c * S) * s ≤ a := by
      nlinarith [mul_nonneg hs0 (le_of_lt (neg_pos.mpr hsign))]
    calc a + b * s + c * s ^ 2 ≤ a + (b + c * S) * s := h1
      _ ≤ a := h2
      _ ≤ max a (a + b * S + c * S ^ 2) := le_max_left _ _
  · have h1 : a + b * s + c * s ^ 2 ≤ a + (b + c * S) * s := by
      nlinarith [mul_nonneg hs0 (by linarith : (0:ℝ) ≤ S - s)]
    have h2 : a + (b + c * S) * s ≤ a + (b + c * S) * S := by
      linarith [mul_le_mul_of_nonneg_left hsS hsign]
    calc a + b * s + c * s ^ 2 ≤ a + (b + c * S) * s := h1
      _ ≤ a + (b + c * S) * S := h2
      _ = a + b * S + c * S ^ 2 := by ring
      _ ≤ max a (a + b * S + c * S ^ 2) := le_max_right _ _

/-─────────────────────────────────────────────────────────────────────────────
  Cubic boundedness: f(u) = a*u+b*u²+c*u³ factors as u*(a+bu+cu²), and
  f(U)-f(u) factors as (U-u)*(a+b(U+u)+c(U²+Uu+u²)) — both pure `ring`
  identities, the algebraic key to everything below.
─────────────────────────────────────────────────────────────────────────────-/

theorem cubic_eq_mul (a b c u : ℝ) : a * u + b * u ^ 2 + c * u ^ 3 = u * (a + b * u + c * u ^ 2) := by
  ring

theorem cubic_diff_eq_mul (a b c U u : ℝ) :
    (a * U + b * U ^ 2 + c * U ^ 3) - (a * u + b * u ^ 2 + c * u ^ 3)
      = (U - u) * (a + b * (U + u) + c * (U ^ 2 + U * u + u ^ 2)) := by
  ring

/-- Discriminant case: if the "u-factored" quadratic AND the "(U-u)-factored"
quadratic are both nonneg (globally, via quad_discrim_nonneg), then f stays
between 0 and f(U) on all of [0,U] — in particular `|f(u)| ≤ f(U) = |f(U)|`
(f(U)≥0 follows automatically from u=U). -/
theorem cubic_tight_pos (a b c U : ℝ) (hc : 0 < c)
    (hdisc_h : b ^ 2 ≤ 4 * a * c)
    (hdisc_g : (b + c * U) ^ 2 ≤ 4 * (a + b * U + c * U ^ 2) * c)
    (u : ℝ) (hu0 : 0 ≤ u) (huU : u ≤ U) :
    0 ≤ a * u + b * u ^ 2 + c * u ^ 3 ∧ a * u + b * u ^ 2 + c * u ^ 3 ≤ a * U + b * U ^ 2 + c * U ^ 3 := by
  have hh := quad_discrim_nonneg a b c hc hdisc_h u
  have hg := quad_discrim_nonneg (a + b * U + c * U ^ 2) (b + c * U) c hc hdisc_g u
  constructor
  · rw [cubic_eq_mul]; exact mul_nonneg hu0 hh
  · have := cubic_diff_eq_mul a b c U u
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ U - u) hg]

/-- Monotonicity case: if a≤0 and the cubic's defining monotonicity condition
`b+3cU≤0` holds, f stays between f(U) (≤0) and 0 on [0,U] — in particular
`|f(u)| ≤ |f(U)|`. -/
theorem cubic_tight_neg (a b c U : ℝ) (hc : 0 < c) (ha : a ≤ 0)
    (hmono : b + 3 * c * U ≤ 0)
    (u : ℝ) (hu0 : 0 ≤ u) (huU : u ≤ U) :
    a * U + b * U ^ 2 + c * U ^ 3 ≤ a * u + b * u ^ 2 + c * u ^ 3 ∧ a * u + b * u ^ 2 + c * u ^ 3 ≤ 0 := by
  have hUnn : 0 ≤ U := le_trans hu0 huU
  have hcU : 0 ≤ c * U := mul_nonneg hc.le hUnn
  have hh : a + b * u + c * u ^ 2 ≤ 0 :=
    quad_mono_nonpos a b c U hc ha (by linarith) u hu0 huU
  have hg : (a + b * U + c * U ^ 2) + (b + c * U) * u + c * u ^ 2 ≤ 0 :=
    quad_mono_nonpos (a + b * U + c * U ^ 2) (b + c * U) c U hc
      (quad_mono_nonpos a b c U hc ha (by linarith) U hUnn le_rfl) (by linarith) u hu0 huU
  constructor
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ U - u)
      (by nlinarith [hg] : (0:ℝ) ≤ -(a + b * (U + u) + c * (U ^ 2 + U * u + u ^ 2)))]
  · rw [cubic_eq_mul]; nlinarith [mul_nonpos_of_nonneg_of_nonpos hu0 hh]

/-─────────────────────────────────────────────────────────────────────────────
  Lipschitz-constant tightening: bounding the symmetric "divided difference"
  k(u1,u2) := a+b(u1+u2)+c(u1²+u1u2+u2²), which satisfies the exact identity
  f(u1)-f(u2) = (u1-u2)*k(u1,u2) (provable by `ring`, used at the call site in
  Pipeline/RadialBoundsTight.lean). Via u1²+u1u2+u2² = (3/4)s²+(1/4)(u1-u2)²
  (s:=u1+u2), k is sandwiched between two quadratics in s alone: ψ(s) :=
  a+bs+(3c/4)s² ≤ k(u1,u2) ≤ a+bs+cs² =: φ(s), for s∈[0,2U].
─────────────────────────────────────────────────────────────────────────────-/

theorem k_bound_pos (a b c U : ℝ) (hc : 0 < c) (hU : 0 ≤ U)
    (hdisc_psi : b ^ 2 ≤ 3 * a * c)
    (u1 u2 : ℝ) (hu1_0 : 0 ≤ u1) (hu1_U : u1 ≤ U) (hu2_0 : 0 ≤ u2) (hu2_U : u2 ≤ U) :
    |a + b * (u1 + u2) + c * (u1 ^ 2 + u1 * u2 + u2 ^ 2)| ≤ max a (a + 2 * b * U + 4 * c * U ^ 2) := by
  have hs0 : (0:ℝ) ≤ u1 + u2 := by linarith
  have hsS : u1 + u2 ≤ 2 * U := by linarith
  have ha_nonneg : 0 ≤ a := by nlinarith [sq_nonneg b, hdisc_psi, hc]
  have hpsi : 0 ≤ a + b * (u1 + u2) + (3 * c / 4) * (u1 + u2) ^ 2 :=
    quad_discrim_nonneg a b (3 * c / 4) (by linarith) (by nlinarith [hdisc_psi]) (u1 + u2)
  have hlow : a + b * (u1 + u2) + (3 * c / 4) * (u1 + u2) ^ 2
      ≤ a + b * (u1 + u2) + c * (u1 ^ 2 + u1 * u2 + u2 ^ 2) := by
    nlinarith [sq_nonneg (u1 - u2)]
  have hphi_chord := quad_chord_upper a b c (2 * U) hc (by linarith) (u1 + u2) hs0 hsS
  have hhigh : a + b * (u1 + u2) + c * (u1 ^ 2 + u1 * u2 + u2 ^ 2)
      ≤ a + b * (u1 + u2) + c * (u1 + u2) ^ 2 := by
    nlinarith [mul_nonneg hu1_0 hu2_0]
  have hmax_nonneg : 0 ≤ max a (a + 2 * b * U + 4 * c * U ^ 2) := le_trans ha_nonneg (le_max_left _ _)
  rw [abs_le]
  refine ⟨by linarith, ?_⟩
  calc a + b * (u1 + u2) + c * (u1 ^ 2 + u1 * u2 + u2 ^ 2) ≤ a + b * (u1 + u2) + c * (u1 + u2) ^ 2 := hhigh
    _ ≤ max a (a + b * (2 * U) + c * (2 * U) ^ 2) := hphi_chord
    _ = max a (a + 2 * b * U + 4 * c * U ^ 2) := by ring_nf

theorem k_bound_neg (a b c U : ℝ) (hc : 0 < c) (hU : 0 ≤ U) (ha : a ≤ 0)
    (hmono : b + 4 * c * U ≤ 0)
    (u1 u2 : ℝ) (hu1_0 : 0 ≤ u1) (hu1_U : u1 ≤ U) (hu2_0 : 0 ≤ u2) (hu2_U : u2 ≤ U) :
    |a + b * (u1 + u2) + c * (u1 ^ 2 + u1 * u2 + u2 ^ 2)| ≤ |a + 2 * b * U + 3 * c * U ^ 2| := by
  have hs0 : (0:ℝ) ≤ u1 + u2 := by linarith
  have hsS : u1 + u2 ≤ 2 * U := by linarith
  have hcU : 0 ≤ c * U := mul_nonneg hc.le hU
  have hmono_psi : b + 2 * (3 * c / 4) * (2 * U) ≤ 0 := by nlinarith [hmono, hcU]
  have hmono' : b + 2 * c * (2 * U) ≤ 0 := by nlinarith [hmono, hcU]
  have hc34 : 0 < (3 * c / 4 : ℝ) := by linarith
  have hpsi_nonpos : a + b * (u1 + u2) + (3 * c / 4) * (u1 + u2) ^ 2 ≤ 0 :=
    quad_mono_nonpos a b (3 * c / 4) (2 * U) hc34 ha hmono_psi (u1 + u2) hs0 hsS
  have hpsi_lower := quad_mono_decreasing_lower a b (3 * c / 4) (2 * U) hc34 hmono_psi (u1 + u2) hs0 hsS
  have hlow : a + b * (u1 + u2) + (3 * c / 4) * (u1 + u2) ^ 2
      ≤ a + b * (u1 + u2) + c * (u1 ^ 2 + u1 * u2 + u2 ^ 2) := by
    nlinarith [sq_nonneg (u1 - u2)]
  have hphi_nonpos : a + b * (u1 + u2) + c * (u1 + u2) ^ 2 ≤ 0 :=
    quad_mono_nonpos a b c (2 * U) hc ha hmono' (u1 + u2) hs0 hsS
  have hhigh : a + b * (u1 + u2) + c * (u1 ^ 2 + u1 * u2 + u2 ^ 2)
      ≤ a + b * (u1 + u2) + c * (u1 + u2) ^ 2 := by
    nlinarith [mul_nonneg hu1_0 hu2_0]
  have hpsiS_eq : a + b * (2 * U) + (3 * c / 4) * (2 * U) ^ 2 = a + 2 * b * U + 3 * c * U ^ 2 := by ring
  rw [abs_le]
  constructor
  · nlinarith [hpsi_lower, hlow, hpsiS_eq, neg_abs_le (a + 2 * b * U + 3 * c * U ^ 2)]
  · have h1 : a + b * (u1 + u2) + c * (u1 ^ 2 + u1 * u2 + u2 ^ 2) ≤ 0 := by linarith [hhigh, hphi_nonpos]
    nlinarith [h1, abs_nonneg (a + 2 * b * U + 3 * c * U ^ 2)]
