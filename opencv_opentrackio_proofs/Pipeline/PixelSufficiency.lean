/-
  Pipeline/PixelSufficiency.lean

  Proves sufficiency: all parameter conversions + ws/w = fx implies full pixel
  x-output agreement between OpenCV and OpenLensIO pipelines.
-/

import DistortionConversion

/-─────────────────────────────────────────────────────────────────────────────
  opencv_openlensio_full_pipeline_pixel_sufficiency

  When all parameter conversions hold AND ws/w = fx, the full (radial +
  tangential + linear-projection) pixel x-output of OpenCV equals the
  corresponding OpenLensIO pixel x-output for every normalised input point.

  OpenCV pixel x:
    fx · (R_cv(r_n)·x' + 2·p1·x'·y' + p2·(r_n² + 2·x'²)) + cx

  OpenLensIO pixel x (at screen point (F·x', F·y'), r_s = F·r_n):
    (ws/w) · (R_oti(r_s)·(F·x') + 2·q1·(F·x')·(F·y') + q2·(r_s² + 2·(F·x')²) + ΔPx) + ws/2

  After substituting all conversions (l_i = k_i_cv/F^(2n), q_i = p_i/F²,
  F = (w/ws)·fx, ΔPx = (w/ws)·(cx − ws/2)) and ws/w = fx, both sides equal:
    fx·R_cv·x' + fx·(2·p1·x'·y' + p2·(r_n² + 2·x'²)) + cx

  where r_n² = x'² + y'².
─────────────────────────────────────────────────────────────────────────────-/

theorem opencv_openlensio_full_pipeline_pixel_sufficiency
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fx cx ws w F ΔPx : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0) (hF : F ≠ 0) (hF_pos : 0 < F)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hq1 : q1 = p1 / F ^ 2) (hq2 : q2 = p2 / F ^ 2)
    (hF_eq : F = (w / ws) * fx) (hΔPx : ΔPx = (w / ws) * (cx - ws / 2))
    (hscale : ws / w = fx)
    (hden : ∀ x' y' : ℝ,
        1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
          + k6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0) :
    ∀ x' y' : ℝ,
      -- OpenCV pixel x-output
      fx * ((1 + k1 * (x' ^ 2 + y' ^ 2) + k2 * (x' ^ 2 + y' ^ 2) ^ 2
               + k3 * (x' ^ 2 + y' ^ 2) ^ 3) /
            (1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
               + k6 * (x' ^ 2 + y' ^ 2) ^ 3) * x'
           + 2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2)) + cx
      =
      -- OpenLensIO pixel x-output (screen point (F·x', F·y'))
      (ws / w) * ((1 + l1 * ((F * x') ^ 2 + (F * y') ^ 2)
                     + l3 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
                     + l5 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3) /
                  (1 + l2 * ((F * x') ^ 2 + (F * y') ^ 2)
                     + l4 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
                     + l6 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3) * (F * x')
                 + 2 * q1 * (F * x') * (F * y')
                 + q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2) + ΔPx)
      + ws / 2 := by
  intro x' y'
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have hF4 : F ^ 4 ≠ 0 := pow_ne_zero _ hF
  have hF6 : F ^ 6 ≠ 0 := pow_ne_zero _ hF
  have hden_xy := hden x' y'
  -- ws = w * fx  (from hscale : ws/w = fx, clearing denominator)
  have hws_eq : ws = w * fx := by
    have h := (div_eq_iff hw).mp hscale
    rw [mul_comm] at h; exact h
  -- fx ≠ 0  (since ws ≠ 0 and w ≠ 0)
  have hfx : fx ≠ 0 := by rw [← hscale]; exact div_ne_zero hws hw
  -- Radial numerator equality: OTI at (F·x', F·y') = CV at (x', y')
  have h_num :
      1 + l1 * ((F * x') ^ 2 + (F * y') ^ 2)
        + l3 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
        + l5 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3 =
      1 + k1 * (x' ^ 2 + y' ^ 2) + k2 * (x' ^ 2 + y' ^ 2) ^ 2
        + k3 * (x' ^ 2 + y' ^ 2) ^ 3 := by
    have hFsq : (F * x') ^ 2 + (F * y') ^ 2 = F ^ 2 * (x' ^ 2 + y' ^ 2) := by ring
    rw [hFsq, hl1, hl3, hl5]; field_simp [hF2, hF4, hF6]
  -- Radial denominator equality
  have h_den :
      1 + l2 * ((F * x') ^ 2 + (F * y') ^ 2)
        + l4 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
        + l6 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3 =
      1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
        + k6 * (x' ^ 2 + y' ^ 2) ^ 3 := by
    have hFsq : (F * x') ^ 2 + (F * y') ^ 2 = F ^ 2 * (x' ^ 2 + y' ^ 2) := by ring
    rw [hFsq, hl2, hl4, hl6]; field_simp [hF2, hF4, hF6]
  -- Both sides now share the CV radial ratio; substitute all parameters and ws
  -- Note: rw [hws_eq] eliminates ws everywhere (including from F = (w/ws)*fx → 1)
  rw [h_num, h_den, hq1, hq2, hΔPx, hF_eq, hws_eq]
  field_simp [hw, hfx, hden_xy]
  ring
