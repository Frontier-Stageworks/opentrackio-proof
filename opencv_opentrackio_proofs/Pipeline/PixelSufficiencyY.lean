/-
  Pipeline/PixelSufficiencyY.lean

  Y-axis mirror of Pipeline/PixelSufficiency.lean. Proves sufficiency: all
  parameter conversions + h_shader/h = fy implies full pixel y-output agreement
  between OpenCV and OpenLensIO pipelines.

  See docs/laps/y-pixel-equivalence/ for the full proof plan and the derivation
  confirming the axis-swap correspondence.
-/

import DistortionConversion

/-─────────────────────────────────────────────────────────────────────────────
  opencv_openlensio_full_pipeline_pixel_sufficiency_y

  When all parameter conversions hold AND h_shader/h = fy, the full (radial +
  tangential + linear-projection) pixel y-output of OpenCV equals the
  corresponding OpenLensIO pixel y-output for every normalised input point.

  OpenCV pixel y:
    fy · (R_cv(r_n)·y' + p1·(r_n² + 2·y'²) + 2·p2·x'·y') + cy

  OpenLensIO pixel y (at screen point (F·x', F·y'), r_s = F·r_n):
    (h_shader/h) · (R_oti(r_s)·(F·y') + q1·(r_s² + 2·(F·y')²) + 2·q2·(F·x')·(F·y') + ΔPy) + h_shader/2

  After substituting all conversions (l_i = k_i_cv/F^(2n), q_i = p_i/F²,
  F = (h/h_shader)·fy, ΔPy = (h/h_shader)·(cy − h_shader/2)) and h_shader/h = fy,
  both sides equal:
    fy·R_cv·y' + fy·(p1·(r_n² + 2·y'²) + 2·p2·x'·y') + cy

  where r_n² = x'² + y'².
─────────────────────────────────────────────────────────────────────────────-/

theorem opencv_openlensio_full_pipeline_pixel_sufficiency_y
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fy cy h_shader h F ΔPy : ℝ)
    (hh : h ≠ 0) (hhs : h_shader ≠ 0) (hF : F ≠ 0) (hF_pos : 0 < F)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hq1 : q1 = p1 / F ^ 2) (hq2 : q2 = p2 / F ^ 2)
    (hF_eq : F = (h / h_shader) * fy) (hΔPy : ΔPy = (h / h_shader) * (cy - h_shader / 2))
    (hscale : h_shader / h = fy)
    (hden : ∀ x' y' : ℝ,
        1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
          + k6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0) :
    ∀ x' y' : ℝ,
      -- OpenCV pixel y-output
      fy * ((1 + k1 * (x' ^ 2 + y' ^ 2) + k2 * (x' ^ 2 + y' ^ 2) ^ 2
               + k3 * (x' ^ 2 + y' ^ 2) ^ 3) /
            (1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
               + k6 * (x' ^ 2 + y' ^ 2) ^ 3) * y'
           + p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) + 2 * p2 * x' * y') + cy
      =
      -- OpenLensIO pixel y-output (screen point (F·x', F·y'))
      (h_shader / h) * ((1 + l1 * ((F * x') ^ 2 + (F * y') ^ 2)
                     + l3 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
                     + l5 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3) /
                  (1 + l2 * ((F * x') ^ 2 + (F * y') ^ 2)
                     + l4 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
                     + l6 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3) * (F * y')
                 + q1 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * y') ^ 2)
                 + 2 * q2 * (F * x') * (F * y') + ΔPy)
      + h_shader / 2 := by
  intro x' y'
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have hF4 : F ^ 4 ≠ 0 := pow_ne_zero _ hF
  have hF6 : F ^ 6 ≠ 0 := pow_ne_zero _ hF
  have hden_xy := hden x' y'
  -- h_shader = h * fy  (from hscale : h_shader/h = fy, clearing denominator)
  have hhs_eq : h_shader = h * fy := by
    have h := (div_eq_iff hh).mp hscale
    rw [mul_comm] at h; exact h
  -- fy ≠ 0  (since h_shader ≠ 0 and h ≠ 0)
  have hfy : fy ≠ 0 := by rw [← hscale]; exact div_ne_zero hhs hh
  -- Radial numerator equality: OTI at (F·x', F·y') = CV at (x', y') — axis-invariant,
  -- verbatim copy of PixelSufficiency.lean's h_num (does not depend on x'/y' labeling)
  have h_num :
      1 + l1 * ((F * x') ^ 2 + (F * y') ^ 2)
        + l3 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
        + l5 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3 =
      1 + k1 * (x' ^ 2 + y' ^ 2) + k2 * (x' ^ 2 + y' ^ 2) ^ 2
        + k3 * (x' ^ 2 + y' ^ 2) ^ 3 := by
    have hFsq : (F * x') ^ 2 + (F * y') ^ 2 = F ^ 2 * (x' ^ 2 + y' ^ 2) := by ring
    rw [hFsq, hl1, hl3, hl5]; field_simp [hF2, hF4, hF6]
  -- Radial denominator equality — axis-invariant, verbatim copy
  have h_den :
      1 + l2 * ((F * x') ^ 2 + (F * y') ^ 2)
        + l4 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
        + l6 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3 =
      1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
        + k6 * (x' ^ 2 + y' ^ 2) ^ 3 := by
    have hFsq : (F * x') ^ 2 + (F * y') ^ 2 = F ^ 2 * (x' ^ 2 + y' ^ 2) := by ring
    rw [hFsq, hl2, hl4, hl6]; field_simp [hF2, hF4, hF6]
  rw [h_num, h_den, hq1, hq2, hΔPy, hF_eq, hhs_eq]
  field_simp [hh, hfy, hden_xy]
  ring
