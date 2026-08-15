/-
  Derivation of the PHYSICALLY-CONSISTENT Tangential Distortion Conversion

  Companion to `DistortionConversion.lean`. That file faithfully formalizes the
  source paper's stated tangential consistency condition and its consequence
  `q1 = p1/F², q2 = p2/F²`. Nothing in that file is modified here.

  This file investigates a suspected physical-semantics error in the paper's
  own tangential derivation. The paper's coordinate map for the *distorted*
  point is ε'_x,d = F·x'' (screen-space distorted coordinate equals F times
  the normalised-space distorted coordinate). Writing x'' = x' + δx_cv and
  ε'_x,d = ε_x + δx_oti with ε_x = F·x':

    ε_x + δx_oti = F·(x' + δx_cv)
    F·x' + δx_oti = F·x' + F·δx_cv
    δx_oti = F·δx_cv

  i.e. the tangential displacement — being *additive*, unlike the
  *multiplicative* radial term — should pick up exactly one factor of F on
  conversion, not zero (as the paper states) and not two (the net effect of
  re-substituting q_i = p_i/F² into the pixel pipeline; see
  `Pipeline/PixelIffCorrected.lean`). The radial term needs no such fix: its
  own outer `x'` factor already carries the F, so l = k/F^(2n) is unaffected.

  This file proves the corrected consistency condition

    F · δx_cv = δx_oti

  implies q1 = p1/F, q2 = p2/F — one power of F, not two — mirroring the
  Layer 1 / Layer 2 structure of `DistortionConversion.lean` exactly.
-/

import DistortionConversion

/-─────────────────────────────────────────────────────────────────────────────
  Layer 1 — Per-term coefficient theorems (physical / corrected scaling)
─────────────────────────────────────────────────────────────────────────────-/

/-
  Tangential q1 conversion (physical) — cross term, F·p1·x'·y' = q1·(Fx')·(Fy').
-/
theorem tangential_q1_conversion_physical
    (p1 q1 F : ℝ)
    (hF : F ≠ 0)
    (hconsist : ∀ x' y' : ℝ, F * (p1 * x' * y') = q1 * (F * x') * (F * y')) :
    q1 = p1 / F := by
  have h11 := hconsist 1 1
  simp only [mul_one] at h11
  -- h11 : F * p1 = q1 * F * F. Cancel one factor of F (division is not a ring
  -- identity; go through mul_right_cancel₀ after a pure ring rearrangement).
  have hcancel : p1 * F = (q1 * F) * F := by linear_combination h11
  have hp1eq : p1 = q1 * F := mul_right_cancel₀ hF hcancel
  rw [eq_div_iff hF]
  exact hp1eq.symm

/-
  Tangential q2 conversion (physical) — radial-shaped term,
  F·p2·(r^2+2x'^2) = q2·((Fr)^2+2(Fx')^2).
-/
theorem tangential_q2_conversion_physical
    (p2 q2 F : ℝ)
    (hF : F ≠ 0)
    (hconsist : ∀ r x' : ℝ,
        F * (p2 * (r ^ 2 + 2 * x' ^ 2)) = q2 * ((F * r) ^ 2 + 2 * (F * x') ^ 2)) :
    q2 = p2 / F := by
  have h10 := hconsist 1 0
  simp only [mul_zero, sq, mul_one, add_zero] at h10
  have hcancel : p2 * F = (q2 * F) * F := by linear_combination h10
  have hp2eq : p2 = q2 * F := mul_right_cancel₀ hF hcancel
  rw [eq_div_iff hF]
  exact hp2eq.symm

/-─────────────────────────────────────────────────────────────────────────────
  Layer 2 — Whole-polynomial iff theorems (physical / corrected scaling)
─────────────────────────────────────────────────────────────────────────────-/

/-
  Whole tangential field conversion (iff), physical scaling.

  F times the full OpenCV tangential δx expression equals the full OpenTrackIO
  tangential δx expression for all x', y' iff q1 = p1/F and q2 = p2/F.
-/
theorem whole_tangential_field_iff_physical
    (p1 p2 q1 q2 F : ℝ)
    (hF : F ≠ 0) :
    (∀ x' y' : ℝ,
        F * (2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2)) =
        2 * q1 * (F * x') * (F * y') +
          q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2)) ↔
    q1 = p1 / F ∧ q2 = p2 / F := by
  constructor
  · intro h
    have h01 := h 0 1
    have h11 := h 1 1
    simp only [mul_zero, zero_mul, mul_one, zero_add] at h01 h11
    norm_num at h01 h11
    -- h01 : F * p2 = q2 * F ^ 2
    have hp2cancel : p2 * F = (q2 * F) * F := by linear_combination h01
    have hp2eq : p2 = q2 * F := mul_right_cancel₀ hF hp2cancel
    rw [hp2eq] at h11
    -- h11 (after substitution) : F * (2*p1 + (q2*F)*4) = 2*q1*F*F + q2*(F^2+F^2+2*F^2)
    have hp1cancel : p1 * F = (q1 * F) * F := by linear_combination h11 / 2
    have hp1eq : p1 = q1 * F := mul_right_cancel₀ hF hp1cancel
    refine ⟨?_, ?_⟩
    · rw [eq_div_iff hF]; exact hp1eq.symm
    · rw [eq_div_iff hF]; exact hp2eq.symm
  · intro ⟨hq1, hq2⟩ x' y'
    rw [hq1, hq2]
    have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
    field_simp [hF2]

/-
  Whole tangential field conversion, 2D (iff), physical scaling.
-/
theorem whole_tangential_field_2d_iff_physical
    (p1 p2 q1 q2 F : ℝ)
    (hF : F ≠ 0) :
    (∀ x' y' : ℝ,
        -- δx
        F * (2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2)) =
          2 * q1 * (F * x') * (F * y') +
            q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2) ∧
        -- δy
        F * (p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) + 2 * p2 * x' * y') =
          q1 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * y') ^ 2) +
            2 * q2 * (F * x') * (F * y')) ↔
    q1 = p1 / F ∧ q2 = p2 / F := by
  constructor
  · intro h
    apply (whole_tangential_field_iff_physical p1 p2 q1 q2 F hF).mp
    intro x' y'
    exact (h x' y').1
  · intro ⟨hq1, hq2⟩ x' y'
    constructor
    · exact (whole_tangential_field_iff_physical p1 p2 q1 q2 F hF).mpr ⟨hq1, hq2⟩ x' y'
    · rw [hq1, hq2]
      have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
      field_simp [hF2]

/-
  Corollary — Full distortion model conversion (iff), physical tangential scaling.

  Radial conjuncts are unchanged from `all_distortion_conversions_iff` (no bug
  there); the tangential conjunct uses the corrected F-scaled consistency
  condition and concludes q1 = p1/F, q2 = p2/F.
-/
theorem all_distortion_conversions_iff_physical
    (k1 k2 k3 k4 k5 k6 : ℝ)
    (l1 l2 l3 l4 l5 l6 : ℝ)
    (p1 p2 q1 q2 F : ℝ)
    (hF : F ≠ 0) :
    (∀ r : ℝ,
        k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6 =
        l1 * (F * r) ^ 2 + l3 * (F * r) ^ 4 + l5 * (F * r) ^ 6) ∧
    (∀ r : ℝ,
        k4 * r ^ 2 + k5 * r ^ 4 + k6 * r ^ 6 =
        l2 * (F * r) ^ 2 + l4 * (F * r) ^ 4 + l6 * (F * r) ^ 6) ∧
    (∀ x' y' : ℝ,
        F * (2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2)) =
          2 * q1 * (F * x') * (F * y') +
            q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2) ∧
        F * (p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) + 2 * p2 * x' * y') =
          q1 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * y') ^ 2) +
            2 * q2 * (F * x') * (F * y')) ↔
    l1 = k1 / F ^ 2 ∧ l3 = k2 / F ^ 4 ∧ l5 = k3 / F ^ 6 ∧
    l2 = k4 / F ^ 2 ∧ l4 = k5 / F ^ 4 ∧ l6 = k6 / F ^ 6 ∧
    q1 = p1 / F ∧ q2 = p2 / F := by
  rw [whole_radial_polynomial_iff k1 k2 k3 l1 l3 l5 F hF,
      whole_radial_polynomial_iff k4 k5 k6 l2 l4 l6 F hF,
      whole_tangential_field_2d_iff_physical p1 p2 q1 q2 F hF]
  constructor
  · intro ⟨⟨h1, h3, h5⟩, ⟨h2, h4, h6⟩, hq1, hq2⟩
    exact ⟨h1, h3, h5, h2, h4, h6, hq1, hq2⟩
  · intro ⟨h1, h3, h5, h2, h4, h6, hq1, hq2⟩
    exact ⟨⟨h1, h3, h5⟩, ⟨h2, h4, h6⟩, hq1, hq2⟩
