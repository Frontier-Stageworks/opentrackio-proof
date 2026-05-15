/-
  Derivation of OpenTrackIO Distortion Parameter Conversions from First Principles

  Source: "Conversion of OpenCV to OpenTrackIO (OpenLensIO) lens calibration parameters"
  SMPTE RIS, corrected 2025-09-02.

  OpenCV and OpenTrackIO use different coordinate spaces for their distortion models:

    OpenCV:      normalised coordinates (x', y') with radius r = sqrt(x'^2 + y'^2)
    OpenTrackIO: screen coordinates (ε'_x,u, ε'_y,u) with radius r_u = F * r

  Radial distortion
  ─────────────────
  OpenCV:      adds k1*r^2 + k2*r^4 + k3*r^6 to each normalised coordinate
  OpenTrackIO: adds l1*r_u^2 + l3*r_u^4 + l5*r_u^6 to each screen coordinate

  Consistency (for all r):
    k1*r^2 + k2*r^4 + k3*r^6 = l1*(F*r)^2 + l3*(F*r)^4 + l5*(F*r)^6

  Tangential distortion
  ─────────────────────
  OpenCV:      δx = 2*p1*x'*y' + p2*(r^2 + 2*x'^2)
               δy = p1*(r^2 + 2*y'^2) + 2*p2*x'*y'
  OpenTrackIO: δx = 2*q1*ε_x*ε_y + q2*(r_u^2 + 2*ε_x^2)
               δy = q1*(r_u^2 + 2*ε_y^2) + 2*q2*ε_x*ε_y
  where ε_x = F*x', ε_y = F*y', r_u^2 = ε_x^2 + ε_y^2 = F^2*(x'^2+y'^2)

  Consistency (for all x', y'):
    2*p1*x'*y' + p2*(x'^2+y'^2+2*x'^2) =
    2*q1*(F*x')*(F*y') + q2*((F*x')^2+(F*y')^2+2*(F*x')^2)

  This file is structured in two layers:

  Layer 1 — Per-term coefficient theorems (useful as lemmas):
    radial_distortion_conversion      ∀r, k*r^(2n) = l*(F*r)^(2n) → l = k/F^(2n)
    tangential_q1_conversion          ∀x'y', p1*x'*y' = q1*(Fx')*(Fy') → q1 = p1/F^2
    tangential_q2_conversion          ∀rx', p2*(r^2+2x'^2) = q2*(...) → q2 = p2/F^2

  Layer 2 — Whole-polynomial iff theorems (the strongest statements):
    whole_radial_polynomial_iff       equality of the full numerator polynomial ↔ coefficients
    whole_tangential_field_iff        equality of the full tangential δx expression ↔ coefficients
    all_distortion_conversions_iff    full model ↔ all eight parameter conversions
-/

import Mathlib.Tactic

/-─────────────────────────────────────────────────────────────────────────────
  Layer 1 — Per-term coefficient theorems
─────────────────────────────────────────────────────────────────────────────-/

/-
  Radial distortion parameter conversion at degree 2n.

  Valid for any n : ℕ including n=0 (which gives l = k trivially).
  The paper instantiates at n=1,2,3 only; see all_distortion_conversions_iff.
-/
theorem radial_distortion_conversion
    (k l F : ℝ) (n : ℕ)
    (hF : F ≠ 0)
    (hconsist : ∀ r : ℝ, k * r ^ (2 * n) = l * (F * r) ^ (2 * n)) :
    l = k / F ^ (2 * n) := by
  have h1 := hconsist 1
  simp only [mul_one, one_pow] at h1
  have hFn : F ^ (2 * n) ≠ 0 := pow_ne_zero _ hF
  field_simp [hFn]
  linarith

/-
  Tangential q1 conversion — cross term p1*x'*y'.
-/
theorem tangential_q1_conversion
    (p1 q1 F : ℝ)
    (hF : F ≠ 0)
    (hconsist : ∀ x' y' : ℝ, p1 * x' * y' = q1 * (F * x') * (F * y')) :
    q1 = p1 / F ^ 2 := by
  have h11 := hconsist 1 1
  simp only [mul_one] at h11
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  field_simp [hF2]
  nlinarith [sq_nonneg F]

/-
  Tangential q2 conversion — radial term p2*(r^2 + 2*x'^2).

  r and x' are treated as independent here.  The witness r=1, x'=0 is
  geometrically realizable (e.g. y'=1 gives r^2 = x'^2 + y'^2 = 1).
-/
theorem tangential_q2_conversion
    (p2 q2 F : ℝ)
    (hF : F ≠ 0)
    (hconsist : ∀ r x' : ℝ, p2 * (r ^ 2 + 2 * x' ^ 2) = q2 * ((F * r) ^ 2 + 2 * (F * x') ^ 2)) :
    q2 = p2 / F ^ 2 := by
  have h10 := hconsist 1 0
  simp only [mul_zero, sq, mul_one, add_zero] at h10
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  field_simp [hF2]
  nlinarith [sq_nonneg F]

/-─────────────────────────────────────────────────────────────────────────────
  Layer 2 — Whole-polynomial iff theorems
─────────────────────────────────────────────────────────────────────────────-/

/-
  Whole radial numerator polynomial conversion (iff).

  The full OpenCV radial numerator k1*r^2 + k2*r^4 + k3*r^6 equals the full
  OpenTrackIO radial numerator l1*(F*r)^2 + l3*(F*r)^4 + l5*(F*r)^6 for all r
  if and only if l1 = k1/F^2, l3 = k2/F^4, l5 = k3/F^6.

  The → direction proves coefficient uniqueness from the whole polynomial.
  It does not assume the terms correspond separately — it derives that they must.

  Proof strategy for →:
    Let ai = ki - li*F^(2i).  The hypothesis gives a1*r^2 + a2*r^4 + a3*r^6 = 0
    for all r.  Specialise at r=1,2,3 to get three equations in a1,a2,a3.
    The 3×3 coefficient matrix has nonzero determinant (Vandermonde-like in
    1^2, 2^2, 3^2 = 1, 4, 9), so nlinarith can derive a1=a2=a3=0.
-/
theorem whole_radial_polynomial_iff
    (k1 k2 k3 l1 l3 l5 F : ℝ)
    (hF : F ≠ 0) :
    (∀ r : ℝ,
        k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6 =
        l1 * (F * r) ^ 2 + l3 * (F * r) ^ 4 + l5 * (F * r) ^ 6) ↔
    l1 = k1 / F ^ 2 ∧ l3 = k2 / F ^ 4 ∧ l5 = k3 / F ^ 6 := by
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have hF4 : F ^ 4 ≠ 0 := pow_ne_zero _ hF
  have hF6 : F ^ 6 ≠ 0 := pow_ne_zero _ hF
  constructor
  · intro h
    -- Specialise at r = 1, 2, 3.
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    simp only [one_pow, mul_one] at h1
    norm_num at h2 h3
    -- The three equations in (l1*F^2, l3*F^4, l5*F^6) form a
    -- Vandermonde-like system with nonzero determinant; nlinarith closes it.
    refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> nlinarith
  · intro ⟨hl1, hl3, hl5⟩ r
    rw [hl1, hl3, hl5]
    field_simp

/-
  Whole tangential field conversion (iff).

  The full OpenCV tangential δx expression
      2*p1*x'*y' + p2*(x'^2 + y'^2 + 2*x'^2)
  equals the full OpenTrackIO tangential δx expression
      2*q1*(F*x')*(F*y') + q2*((F*x')^2 + (F*y')^2 + 2*(F*x')^2)
  for all x', y' if and only if q1 = p1/F^2 and q2 = p2/F^2.

  Note: r^2 = x'^2 + y'^2 is substituted directly, making r and (x',y')
  geometrically consistent.  The expression uses the full 2D coordinates.

  Proof strategy for →:
    Specialise at (x',y') = (0,1) to isolate q2 (cross term vanishes).
    Specialise at (x',y') = (1,1) with q2 known to isolate q1.
-/
theorem whole_tangential_field_iff
    (p1 p2 q1 q2 F : ℝ)
    (hF : F ≠ 0) :
    (∀ x' y' : ℝ,
        2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2) =
        2 * q1 * (F * x') * (F * y') +
          q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2)) ↔
    q1 = p1 / F ^ 2 ∧ q2 = p2 / F ^ 2 := by
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  constructor
  · intro h
    -- (0,1): cross term vanishes, isolates q2.
    have h01 := h 0 1
    -- (1,0): also isolates q2 from the other side.
    have h10 := h 1 0
    -- (1,1): uses both q1 and q2.
    have h11 := h 1 1
    simp only [mul_zero, zero_mul, mul_one, zero_add] at h01 h10 h11
    norm_num at h01 h10 h11
    refine ⟨?_, ?_⟩ <;> field_simp <;> nlinarith
  · intro ⟨hq1, hq2⟩ x' y'
    rw [hq1, hq2]
    field_simp

/-
  Whole tangential field conversion, 2D (iff).

  The full OpenCV tangential vector field (δx AND δy) equals the full OpenTrackIO
  tangential vector field for all (x', y') if and only if q1 = p1/F^2 and q2 = p2/F^2.

  δx_opencv = 2*p1*x'*y'      + p2*(r^2 + 2*x'^2)   where r^2 = x'^2 + y'^2
  δy_opencv = p1*(r^2 + 2*y'^2) + 2*p2*x'*y'

  δx and δy share the same parameters p1,p2 (resp. q1,q2), so requiring both
  components to agree over all (x',y') forces the same conclusion as δx alone.
  The combined theorem removes any objection that only half the vector field was
  formalized.

  The → direction is proved by reducing to whole_tangential_field_iff via the δx
  component, then confirming δy is automatically satisfied.
-/
theorem whole_tangential_field_2d_iff
    (p1 p2 q1 q2 F : ℝ)
    (hF : F ≠ 0) :
    (∀ x' y' : ℝ,
        -- δx
        2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2) =
          2 * q1 * (F * x') * (F * y') +
            q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2) ∧
        -- δy
        p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) + 2 * p2 * x' * y' =
          q1 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * y') ^ 2) +
            2 * q2 * (F * x') * (F * y')) ↔
    q1 = p1 / F ^ 2 ∧ q2 = p2 / F ^ 2 := by
  constructor
  · intro h
    -- The δx component alone is sufficient; extract it and apply the 1D theorem.
    apply (whole_tangential_field_iff p1 p2 q1 q2 F hF).mp
    intro x' y'
    exact (h x' y').1
  · intro ⟨hq1, hq2⟩ x' y'
    constructor
    · exact (whole_tangential_field_iff p1 p2 q1 q2 F hF).mpr ⟨hq1, hq2⟩ x' y'
    · rw [hq1, hq2]; field_simp

/-
  Corollary — Full distortion model conversion (iff).

  The complete OpenCV radial numerator polynomials (numerator and denominator
  treated separately, which implies equality of the rational radial factor under
  nonzero denominators) and the full 2D tangential vector field equal the
  corresponding OpenTrackIO expressions for all coordinates if and only if all
  eight distortion parameters convert by the 1/F^(2n) scaling law.
-/
theorem all_distortion_conversions_iff
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
        2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2) =
          2 * q1 * (F * x') * (F * y') +
            q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2) ∧
        p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) + 2 * p2 * x' * y' =
          q1 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * y') ^ 2) +
            2 * q2 * (F * x') * (F * y')) ↔
    l1 = k1 / F ^ 2 ∧ l3 = k2 / F ^ 4 ∧ l5 = k3 / F ^ 6 ∧
    l2 = k4 / F ^ 2 ∧ l4 = k5 / F ^ 4 ∧ l6 = k6 / F ^ 6 ∧
    q1 = p1 / F ^ 2 ∧ q2 = p2 / F ^ 2 := by
  rw [whole_radial_polynomial_iff k1 k2 k3 l1 l3 l5 F hF,
      whole_radial_polynomial_iff k4 k5 k6 l2 l4 l6 F hF,
      whole_tangential_field_2d_iff p1 p2 q1 q2 F hF]
  constructor
  · intro ⟨⟨h1, h3, h5⟩, ⟨h2, h4, h6⟩, hq1, hq2⟩
    exact ⟨h1, h3, h5, h2, h4, h6, hq1, hq2⟩
  · intro ⟨h1, h3, h5, h2, h4, h6, hq1, hq2⟩
    exact ⟨⟨h1, h3, h5⟩, ⟨h2, h4, h6⟩, hq1, hq2⟩

/-
  Theorem — Radial coefficient conversions imply rational factor equality.

  The OpenCV rational radial factor is:
      (1 + k1*r^2 + k2*r^4 + k3*r^6) / (1 + k4*r^2 + k5*r^4 + k6*r^6)

  The OpenTrackIO rational radial factor (in terms of r_u = F*r) is:
      (1 + l1*r_u^2 + l3*r_u^4 + l5*r_u^6) / (1 + l2*r_u^2 + l4*r_u^4 + l6*r_u^6)

  If the numerator and denominator polynomial conversions hold (as proved in
  all_distortion_conversions_iff), then the two rational factors agree at r.

  Note: in ℝ, equality of division expressions holds syntactically once numerators
  and denominators are equal, without requiring nonzero denominators.  The nonzero
  denominator condition is only needed if reasoning about the *value* of the quotient.

  Note: this is a one-way theorem. The rational factor equality is a consequence
  of the coefficient conversions, but not equivalent to them — different coefficient
  sets can yield equal rational functions.  The coefficient theorems are the stronger
  (and more useful) result for parameter conversion purposes.
-/
theorem radial_coefficients_imply_rational_factor_equality
    (k1 k2 k3 k4 k5 k6 l1 l3 l5 l2 l4 l6 F : ℝ)
    (r : ℝ)
    (hnum : k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6 =
            l1 * (F * r) ^ 2 + l3 * (F * r) ^ 4 + l5 * (F * r) ^ 6)
    (hden : k4 * r ^ 2 + k5 * r ^ 4 + k6 * r ^ 6 =
            l2 * (F * r) ^ 2 + l4 * (F * r) ^ 4 + l6 * (F * r) ^ 6) :
    (1 + k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6) /
    (1 + k4 * r ^ 2 + k5 * r ^ 4 + k6 * r ^ 6) =
    (1 + l1 * (F * r) ^ 2 + l3 * (F * r) ^ 4 + l5 * (F * r) ^ 6) /
    (1 + l2 * (F * r) ^ 2 + l4 * (F * r) ^ 4 + l6 * (F * r) ^ 6) := by
  have hd_cv : 1 + k4 * r ^ 2 + k5 * r ^ 4 + k6 * r ^ 6 =
               1 + l2 * (F * r) ^ 2 + l4 * (F * r) ^ 4 + l6 * (F * r) ^ 6 := by linarith
  have hn_cv : 1 + k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6 =
               1 + l1 * (F * r) ^ 2 + l3 * (F * r) ^ 4 + l5 * (F * r) ^ 6 := by linarith
  rw [hn_cv, hd_cv]
