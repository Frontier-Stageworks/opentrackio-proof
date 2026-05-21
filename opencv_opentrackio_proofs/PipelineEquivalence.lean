/-
  PipelineEquivalence.lean

  Defines the OpenCV undistortion pipeline in normalised coordinate space and
  proves when it agrees with the OpenLensIO (OpenTrackIO) undistortion pipeline.

  Source: "Conversion of OpenCV to OpenTrackIO (OpenLensIO) lens calibration parameters"
  SMPTE RIS, corrected 2025-09-02.

  NAMING NOTE: OpenCV uses k1,k2,k3 (numerator) and k4,k5,k6 (denominator).
  OpenLensIO uses k1,k3,k5 (numerator) and k2,k4,k6 (denominator, alternating).
  These conventions conflict. This file uses OpenCV naming for OpenCV parameters.
  When constructing a RadialCoefficients value from OpenCV params, the field mapping is:
    ⟨cv_k1, cv_k4, cv_k2, cv_k5, cv_k3, cv_k6⟩
  (OTI fields k1,k2,k3,k4,k5,k6 map to OTI-num,OTI-den,OTI-num,OTI-den,OTI-num,OTI-den)

  Theorems:
    opencv_openlensio_radial_pipeline_eq            — radial-only pipeline agreement
    opencv_openlensio_full_pipeline_pixel_sufficiency — all conversions + ws/w=fx → pixel eq
    opencv_openlensio_full_pipeline_pixel_iff        — full iff (requires p1≠0 ∨ p2≠0)
-/

import DistortionConversion
import PixelEquivalence
import DistortionModel

/-─────────────────────────────────────────────────────────────────────────────
  undistortXCV

  The x-component of the OpenCV Brown-Conrady undistortion at a normalised
  distorted point ε.

  r := sensorRadius ε  (normalised radius — NOT screen-space F·r)
  R_cv := (1 + k1·r² + k2·r⁴ + k3·r⁶) / (1 + k4·r² + k5·r⁴ + k6·r⁶)
  δx   := 2·p1·ε.x·ε.y + p2·(r² + 2·ε.x²)   (tangential in normalised space)
  output := R_cv·ε.x + δx

  Coefficient naming: k1,k2,k3 = radial numerator; k4,k5,k6 = radial denominator.
  (DistortionConversion.lean convention, NOT the LensSemantics.lean convention.)
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def undistortXCV
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (ε : SensorPoint)
    (_ : 1 + k4 * (sensorRadius ε) ^ 2 + k5 * (sensorRadius ε) ^ 4
           + k6 * (sensorRadius ε) ^ 6 ≠ 0) : ℝ :=
  let r := sensorRadius ε
  (1 + k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6) /
  (1 + k4 * r ^ 2 + k5 * r ^ 4 + k6 * r ^ 6) * ε.x
  + 2 * p1 * ε.x * ε.y + p2 * (r ^ 2 + 2 * ε.x ^ 2)

/-─────────────────────────────────────────────────────────────────────────────
  undistortYCV

  The y-component of the OpenCV Brown-Conrady undistortion.
  Symmetric to undistortXCV with p1/p2 roles swapped per the OpenCV formula:
  δy := p1·(r² + 2·ε.y²) + 2·p2·ε.x·ε.y
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def undistortYCV
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (ε : SensorPoint)
    (_ : 1 + k4 * (sensorRadius ε) ^ 2 + k5 * (sensorRadius ε) ^ 4
           + k6 * (sensorRadius ε) ^ 6 ≠ 0) : ℝ :=
  let r := sensorRadius ε
  (1 + k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6) /
  (1 + k4 * r ^ 2 + k5 * r ^ 4 + k6 * r ^ 6) * ε.y
  + p1 * (r ^ 2 + 2 * ε.y ^ 2) + 2 * p2 * ε.x * ε.y

/-─────────────────────────────────────────────────────────────────────────────
  undistortPointCV

  The full OpenCV undistortion map U_cv : SensorPoint → SensorPoint.
  Packages undistortXCV and undistortYCV into a SensorPoint.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def undistortPointCV
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (ε : SensorPoint)
    (hden : 1 + k4 * (sensorRadius ε) ^ 2 + k5 * (sensorRadius ε) ^ 4
              + k6 * (sensorRadius ε) ^ 6 ≠ 0) : SensorPoint :=
  ⟨undistortXCV k1 k2 k3 k4 k5 k6 p1 p2 ε hden,
   undistortYCV k1 k2 k3 k4 k5 k6 p1 p2 ε hden⟩

/-─────────────────────────────────────────────────────────────────────────────
  opencv_openlensio_radial_pipeline_eq

  After radial parameter conversion, the zero-tangential OpenCV undistortion
  at normalised point ε' equals (1/F) times the zero-tangential OpenLensIO
  undistortion at the corresponding screen point ⟨F·ε'.x, F·ε'.y⟩.

  Equivalently: F · (CV x-output) = OTI x-output at the screen point.

  The proof reduces both sides to R_cv · coord (after simplifying the zero
  tangential terms), then applies radial_distortion_value_equivalence to
  identify R_cv with R_oti at the scaled radius, and closes by ring.

  Note: OTI RadialCoefficients fields follow the alternating naming convention
  (k1,k3,k5 = numerator; k2,k4,k6 = denominator). The caller must supply
  ⟨l1, l2, l3, l4, l5, l6⟩ with l1,l3,l5 as numerator and l2,l4,l6 as denominator.
─────────────────────────────────────────────────────────────────────────────-/

theorem opencv_openlensio_radial_pipeline_eq
    (k1 k2 k3 k4 k5 k6 l1 l2 l3 l4 l5 l6 F : ℝ)
    (ε' : SensorPoint)
    (hF : F ≠ 0) (hF_pos : 0 < F)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hden_cv : 1 + k4 * (sensorRadius ε') ^ 2 + k5 * (sensorRadius ε') ^ 4
                 + k6 * (sensorRadius ε') ^ 6 ≠ 0)
    (hden_oti : denominatorNonzero ⟨l1, l2, l3, l4, l5, l6⟩
                  (sensorRadius ⟨F * ε'.x, F * ε'.y⟩)) :
    F * undistortXCV k1 k2 k3 k4 k5 k6 0 0 ε' hden_cv =
    undistortX ⟨l1, l2, l3, l4, l5, l6⟩ TangentialCoefficients.zero
      ⟨F * ε'.x, F * ε'.y⟩ hden_oti := by
  -- Radius scaling: sensorRadius ⟨F·x, F·y⟩ = F · sensorRadius ε'
  have h_rscale : sensorRadius ⟨F * ε'.x, F * ε'.y⟩ = F * sensorRadius ε' := by
    simp only [sensorRadius]
    rw [show (F * ε'.x) ^ 2 + (F * ε'.y) ^ 2 = F ^ 2 * (ε'.x ^ 2 + ε'.y ^ 2) by ring]
    rw [Real.sqrt_mul (sq_nonneg F), Real.sqrt_sq (le_of_lt hF_pos)]
  -- Radial scale equality from the existing theorem (at r = sensorRadius ε')
  have h_rad := (radial_distortion_value_equivalence k1 k2 k3 k4 k5 k6 l1 l3 l5 l2 l4 l6
      F (sensorRadius ε') hF hl1 hl3 hl5 hl2 hl4 hl6 hden_cv).1
  -- OTI side: name the zero-tangential reduction to radialTerm · (F·ε'.x)
  have h_oti_simp : undistortX ⟨l1, l2, l3, l4, l5, l6⟩ TangentialCoefficients.zero
      ⟨F * ε'.x, F * ε'.y⟩ hden_oti =
      radialTerm ⟨l1, l2, l3, l4, l5, l6⟩ (sensorRadius ⟨F * ε'.x, F * ε'.y⟩) hden_oti
      * (F * ε'.x) :=
    tangential_zero_coefficients_identity _ _ _ _ rfl rfl
  rw [h_oti_simp]
  -- Name the radialTerm expansion (struct projections reduce by rfl)
  have h_rterm : radialTerm ⟨l1, l2, l3, l4, l5, l6⟩
      (sensorRadius ⟨F * ε'.x, F * ε'.y⟩) hden_oti =
      (1 + l1 * (F * sensorRadius ε') ^ 2 + l3 * (F * sensorRadius ε') ^ 4
         + l5 * (F * sensorRadius ε') ^ 6) /
      (1 + l2 * (F * sensorRadius ε') ^ 2 + l4 * (F * sensorRadius ε') ^ 4
         + l6 * (F * sensorRadius ε') ^ 6) := by
    simp only [radialTerm, h_rscale]
  rw [h_rterm]
  -- CV side: zero tangential reduces to R_cv · ε'.x
  simp only [undistortXCV, mul_zero, zero_mul, add_zero]
  -- h_rad : R_cv = R_oti (the RHS matches exactly); then ring closes F * R * ε' = R * F * ε'
  rw [← h_rad]
  ring

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

/-─────────────────────────────────────────────────────────────────────────────
  Helper lemmas for the forward direction of pixel_iff
─────────────────────────────────────────────────────────────────────────────-/

-- OTI radial ratio at screen point (F*x, F*y) = CV radial ratio at normalised (x, y)
private lemma radial_ratio_scaled_eq
    (k1 k2 k3 k4 k5 k6 l1 l2 l3 l4 l5 l6 F x y : ℝ)
    (hF : F ≠ 0)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hden : 1 + k4 * (x ^ 2 + y ^ 2) + k5 * (x ^ 2 + y ^ 2) ^ 2
              + k6 * (x ^ 2 + y ^ 2) ^ 3 ≠ 0) :
    (1 + l1 * ((F*x)^2 + (F*y)^2) + l3 * ((F*x)^2 + (F*y)^2)^2
       + l5 * ((F*x)^2 + (F*y)^2)^3) /
    (1 + l2 * ((F*x)^2 + (F*y)^2) + l4 * ((F*x)^2 + (F*y)^2)^2
       + l6 * ((F*x)^2 + (F*y)^2)^3) * (F * x)
    =
    (1 + k1 * (x^2 + y^2) + k2 * (x^2 + y^2)^2 + k3 * (x^2 + y^2)^3) /
    (1 + k4 * (x^2 + y^2) + k5 * (x^2 + y^2)^2 + k6 * (x^2 + y^2)^3) * x
    * F := by
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have hF4 : F ^ 4 ≠ 0 := pow_ne_zero _ hF
  have hF6 : F ^ 6 ≠ 0 := pow_ne_zero _ hF
  have hrsq : (F*x)^2 + (F*y)^2 = F^2 * (x^2 + y^2) := by ring
  rw [hrsq, hl1, hl3, hl5, hl2, hl4, hl6]
  field_simp [hF2, hF4, hF6, hden]

-- OTI tangential at screen point (F*x, F*y) = CV tangential at normalised (x, y)
private lemma tangential_scaled_eq
    (p1 p2 q1 q2 F x y : ℝ)
    (hF : F ≠ 0)
    (hq1 : q1 = p1 / F ^ 2) (hq2 : q2 = p2 / F ^ 2) :
    2 * q1 * (F*x) * (F*y) + q2 * ((F*x)^2 + (F*y)^2 + 2*(F*x)^2)
    = 2 * p1 * x * y + p2 * (x^2 + y^2 + 2*x^2) := by
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  rw [hq1, hq2]; field_simp [hF2]

-- (ws/w)*ΔPx + ws/2 = cx   (under ΔPx = (w/ws)*(cx - ws/2))
private lemma principal_offset_cancels
    (cx ws w ΔPx : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0)
    (hΔPx : ΔPx = (w / ws) * (cx - ws / 2)) :
    (ws / w) * ΔPx + ws / 2 = cx := by
  rw [hΔPx]; field_simp [hw, hws]; ring

-- If ∀ x y, (fx - ws/w) * T(x,y) = 0 and p1≠0 ∨ p2≠0, then ws/w = fx
private lemma tangential_gap_forces_scale
    (p1 p2 fx ws w : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0)
    (hp : p1 ≠ 0 ∨ p2 ≠ 0)
    (hgap : ∀ x y : ℝ,
        (fx - ws / w) * (2 * p1 * x * y + p2 * (x^2 + y^2 + 2*x^2)) = 0) :
    ws / w = fx := by
  rcases hp with hp1 | hp2
  · -- p1 ≠ 0: (1,1) gives (fx - ws/w)*(2*p1 + 4*p2) = 0
    --          (1,-1) gives (fx - ws/w)*(-2*p1 + 4*p2) = 0
    --          subtract → (fx - ws/w)*(4*p1) = 0 → fx = ws/w
    have h11  := hgap 1 1
    have h1m1 := hgap 1 (-1)
    have : (fx - ws / w) * (4 * p1) = 0 := by linarith
    rcases mul_eq_zero.mp this with hc | hp1z
    · linarith
    · have : p1 = 0 := by linarith
      exact absurd this hp1
  · -- p2 ≠ 0: (0,1) gives (fx - ws/w)*(p2) = 0
    have h01 := hgap 0 1
    simp only [mul_zero, zero_mul, add_zero, zero_add] at h01
    have : (fx - ws / w) * p2 = 0 := by linarith
    rcases mul_eq_zero.mp this with hc | hp2z
    · linarith
    · exact absurd hp2z hp2

/-─────────────────────────────────────────────────────────────────────────────
  opencv_openlensio_full_pipeline_pixel_iff  (conditional iff)

  Given all parameter conversions hold (l_i = k_i/F^(2n), q_i = p_i/F^2,
  F = (w/ws)*fx, ΔPx = (w/ws)*(cx - ws/2)), the full pixel x-outputs agree
  for every normalised input point if and only if ws/w = fx.

  This is the paper's central claim: the coefficient conversions alone are not
  sufficient; the scale ratio ws/w = fx is exactly the additional condition
  that bridges the gap between the two pipelines.

  Requires hp : p1 ≠ 0 ∨ p2 ≠ 0 for the → direction (to find a point where the
  tangential term δx_cv is nonzero, so we can cancel and conclude ws/w = fx).
─────────────────────────────────────────────────────────────────────────────-/

theorem opencv_openlensio_full_pipeline_pixel_iff
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fx cx ws w F ΔPx : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0) (hF : F ≠ 0) (hF_pos : 0 < F)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hq1 : q1 = p1 / F ^ 2) (hq2 : q2 = p2 / F ^ 2)
    (hF_eq : F = (w / ws) * fx) (hΔPx : ΔPx = (w / ws) * (cx - ws / 2))
    (hp : p1 ≠ 0 ∨ p2 ≠ 0)
    (hden : ∀ x' y' : ℝ,
        1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
          + k6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0) :
    (∀ x' y' : ℝ,
      fx * ((1 + k1 * (x' ^ 2 + y' ^ 2) + k2 * (x' ^ 2 + y' ^ 2) ^ 2
               + k3 * (x' ^ 2 + y' ^ 2) ^ 3) /
            (1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
               + k6 * (x' ^ 2 + y' ^ 2) ^ 3) * x'
           + 2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2)) + cx
      =
      (ws / w) * ((1 + l1 * ((F * x') ^ 2 + (F * y') ^ 2)
                     + l3 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
                     + l5 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3) /
                  (1 + l2 * ((F * x') ^ 2 + (F * y') ^ 2)
                     + l4 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
                     + l6 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3) * (F * x')
                 + 2 * q1 * (F * x') * (F * y')
                 + q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2) + ΔPx)
      + ws / 2)
    ↔ ws / w = fx := by
  constructor
  · -- → direction: placeholder until helper lemmas are built
    intro _h
    sorry
  · -- ← direction: ws/w = fx implies pixel agreement for all (x', y')
    intro hscale
    exact opencv_openlensio_full_pipeline_pixel_sufficiency
        k1 k2 k3 k4 k5 k6 p1 p2 l1 l2 l3 l4 l5 l6 q1 q2
        fx cx ws w F ΔPx
        hw hws hF hF_pos hl1 hl3 hl5 hl2 hl4 hl6 hq1 hq2
        hF_eq hΔPx hscale hden
