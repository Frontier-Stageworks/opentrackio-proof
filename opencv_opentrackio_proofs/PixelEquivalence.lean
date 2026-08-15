/-
  Pixel Equivalence Theorems for OpenCV and OpenTrackIO Camera Models

  Source: "Conversion of OpenCV to OpenTrackIO (OpenLensIO) lens calibration parameters"
  SMPTE RIS, corrected 2025-09-02.

  This file proves two semantic preservation theorems:

    1. linear_projection_pixel_equivalence_2d_iff
         The linear (pinhole) projection is identical in both models for all input
         points iff the published principal-point and focal-length conversions hold.
         This is principal_point_conversion_2d_iff restated in pipeline form.

    2. radial_distortion_value_equivalence
         The rational radial scale factor has the same value in both models at
         corresponding radii (r in OpenCV, r_u = F*r in OpenTrackIO), when the
         published coefficient conversions hold.  Also derives that the OpenTrackIO
         denominator is nonzero whenever the OpenCV denominator is.

  Scope and limitations
  ─────────────────────
  A full end-to-end pipeline theorem composing linear projection and distortion
  requires specifying how distortion output feeds into pixel coordinates in each
  model.  The OpenCV tangential terms operate in normalised space; the OpenTrackIO
  tangential terms operate in screen space.  When expanded with the converted
  parameters q_i = p_i/F², the pixel-formula scaling (ws/w) applies to the
  resulting normalised-scale terms, yielding (ws/w)*p_i rather than fx*p_i.
  These are equal only when ws/w = fx, which is not generally true.

  The paper specifies parameter conversion but does not fully fix the composition
  semantics.  The full pipeline iff is proved in Pipeline/PixelIff.lean as a
  conditional: given all parameter conversions, pixel x-output agreement for all
  inputs holds if and only if ws/w = fx.  This additional scale condition is
  necessary (requires p1 ≠ 0 ∨ p2 ≠ 0 to derive) and sufficient.
  The y-axis analogue is structurally identical and not separately stated.
-/

import Mathlib.Tactic
import PrincipalPointConversion

/-
  Theorem 1 — Linear pixel equivalence is exactly characterized by the conversion
  formulas (necessary and sufficient).

  The linear OpenCV projection  u = fx*x + cx,  v = fy*y + cy
  agrees with the OpenTrackIO projection
    u = (ws/w)*(F*x + ΔPx) + ws/2,  v = (hs/h)*(F*y + ΔPy) + hs/2
  for ALL input points (x, y) if and only if the published conversion formulas hold.

  This is a direct restatement of principal_point_conversion_2d_iff in pipeline form.
-/
theorem linear_projection_pixel_equivalence_2d_iff
    (w h w_shader h_shader fx fy cx cy F ΔPx ΔPy : ℝ)
    (hw   : w ≠ 0) (hh   : h ≠ 0)
    (hw_s : w_shader ≠ 0) (hh_s : h_shader ≠ 0) :
    (∀ x y : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2 ∧
        fy * y + cy = (h_shader / h) * (F * y + ΔPy) + h_shader / 2) ↔
    F   = (w / w_shader) * fx  ∧
    ΔPx = (w / w_shader) * (cx - w_shader / 2) ∧
    F   = (h / h_shader) * fy  ∧
    ΔPy = (h / h_shader) * (cy - h_shader / 2) :=
  principal_point_conversion_2d_iff
    w h w_shader h_shader fx fy cx cy F ΔPx ΔPy hw hh hw_s hh_s

/-
  Theorem 2 — Radial distortion scale value is preserved under parameter conversion.

  Given the published coefficient conversions l_i = k_i/F^(2n), the rational radial
  scale factor evaluated at screen radius r_u = F*r equals the OpenCV radial scale
  factor evaluated at normalised radius r.

  The theorem also derives that the OpenTrackIO denominator is nonzero whenever the
  OpenCV denominator is, making the modeling purpose of hden_cv explicit.
-/
theorem radial_distortion_value_equivalence
    (k1 k2 k3 k4 k5 k6 l1 l3 l5 l2 l4 l6 F r : ℝ)
    (hF  : F ≠ 0)
    (hl1 : l1 = k1 / F^2) (hl3 : l3 = k2 / F^4) (hl5 : l5 = k3 / F^6)
    (hl2 : l2 = k4 / F^2) (hl4 : l4 = k5 / F^4) (hl6 : l6 = k6 / F^6)
    (hden_cv : 1 + k4*r^2 + k5*r^4 + k6*r^6 ≠ 0) :
    -- OpenCV radial scale at normalised radius r equals OpenTrackIO scale at r_u = F*r
    (1 + k1*r^2 + k2*r^4 + k3*r^6) / (1 + k4*r^2 + k5*r^4 + k6*r^6) =
    (1 + l1*(F*r)^2 + l3*(F*r)^4 + l5*(F*r)^6) /
    (1 + l2*(F*r)^2 + l4*(F*r)^4 + l6*(F*r)^6) ∧
    -- The OpenTrackIO denominator is nonzero whenever the OpenCV denominator is
    1 + l2*(F*r)^2 + l4*(F*r)^4 + l6*(F*r)^6 ≠ 0 := by
  have hF2 : F^2 ≠ 0 := pow_ne_zero _ hF
  have hF4 : F^4 ≠ 0 := pow_ne_zero _ hF
  have hF6 : F^6 ≠ 0 := pow_ne_zero _ hF
  have hnum : 1 + k1*r^2 + k2*r^4 + k3*r^6 =
              1 + l1*(F*r)^2 + l3*(F*r)^4 + l5*(F*r)^6 := by
    rw [hl1, hl3, hl5]; field_simp [hF2, hF4, hF6]
  have hden : 1 + k4*r^2 + k5*r^4 + k6*r^6 =
              1 + l2*(F*r)^2 + l4*(F*r)^4 + l6*(F*r)^6 := by
    rw [hl2, hl4, hl6]; field_simp [hF2, hF4, hF6]
  have hden_oti : 1 + l2*(F*r)^2 + l4*(F*r)^4 + l6*(F*r)^6 ≠ 0 := hden ▸ hden_cv
  exact ⟨by rw [hnum, hden], hden_oti⟩
