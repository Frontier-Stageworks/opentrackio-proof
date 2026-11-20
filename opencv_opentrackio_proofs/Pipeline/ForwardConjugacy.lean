/-
  Pipeline/ForwardConjugacy.lean

  The two-dimensional, composed-function forward conjugacy between OpenCV's
  and OpenTrackIO's (corrected) forward-distortion maps:

    distortPointOTI (ScreenScale F ε) = ScreenScale F (distortPointCV ε)

  i.e. D_oti ∘ S_F = S_F ∘ D_cv, stated pointwise (the pointwise form of the
  composed-function identity D_oti = S_F ∘ D_cv ∘ S_F⁻¹, since S_F is a
  bijection — see InverseConjugacy.lean for the abstract conjugacy-of-inverses
  step built on this fact).

  This is a DISTORTION-LEVEL statement (SensorPoint → SensorPoint, no fx/cx/
  ws/w/h_shader/h pixel mapping), derived from — not restated as — the
  existing PIXEL-LEVEL theorems `opencv_openlensio_full_pipeline_pixel_corrected`
  (PixelIffCorrected.lean) and `opencv_openlensio_full_pipeline_pixel_corrected_y`
  (PixelIffCorrectedY.lean), by algebraically unwrapping the shared `+cx`/`+cy`
  offset and the `fx`/`fy` pixel scale from each. Neither file is modified.

  A genuine SINGLE-SCALE two-dimensional statement needs ONE F shared by both
  components, which requires BOTH `F = (w/ws)*fx` AND `F = (h/h_shader)*fy` to
  hold simultaneously — these are taken as two explicit, separate hypotheses
  (hF_eq_x, hF_eq_y) rather than derived from `single_focal_length_compatibility`
  (SQ-CV-04; out of scope here — simpler, and no weaker, to state the shared-F
  requirement directly, since that is exactly what a real single-focal-length
  camera already satisfies by construction).
-/

import Pipeline.OpenTrackIOModel
import Pipeline.PixelIffCorrectedY

/-─────────────────────────────────────────────────────────────────────────────
  ScreenScale

  S_F(ε) = (F·ε.x, F·ε.y) — the coordinate scaling relating OpenCV's
  normalised plane to OpenTrackIO's screen plane (ε'_u = F·x', conversion
  paper p.2 / OpenLensIO base spec Eq.9).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def ScreenScale (F : ℝ) (ε : SensorPoint) : SensorPoint :=
  ⟨F * ε.x, F * ε.y⟩

/-─────────────────────────────────────────────────────────────────────────────
  opencv_openlensio_forward_point_corrected

  The two-dimensional forward conjugacy, both coordinates at once, proved
  from the (corrected-tangential-scaling) x and y pixel theorems — not
  assumed. `hden` is the same free, per-point, universally-quantified
  denominator-nonzero hypothesis every pipeline theorem in this repository
  already takes; `hden_cv`/`hden_oti` are its SensorPoint-indexed restatements
  at ε / ScreenScale F ε, required because `distortPointCV`/`distortPointOTI`
  take their domain hypothesis in `sensorRadius`-squared form.
─────────────────────────────────────────────────────────────────────────────-/

theorem opencv_openlensio_forward_point_corrected
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fx fy cx cy ws w h_shader h F ΔPx ΔPy : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0) (hh : h ≠ 0) (hhs : h_shader ≠ 0)
    (hF : F ≠ 0) (hF_pos : 0 < F)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hq1 : q1 = p1 / F) (hq2 : q2 = p2 / F)
    (hF_eq_x : F = (w / ws) * fx) (hF_eq_y : F = (h / h_shader) * fy)
    (hΔPx : ΔPx = (w / ws) * (cx - ws / 2)) (hΔPy : ΔPy = (h / h_shader) * (cy - h_shader / 2))
    (hden : ∀ x' y' : ℝ,
        1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
          + k6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0)
    (ε : SensorPoint)
    (hden_cv : 1 + k4 * (sensorRadius ε) ^ 2 + k5 * (sensorRadius ε) ^ 4
                 + k6 * (sensorRadius ε) ^ 6 ≠ 0)
    (hden_oti : 1 + l2 * (sensorRadius (ScreenScale F ε)) ^ 2
                  + l4 * (sensorRadius (ScreenScale F ε)) ^ 4
                  + l6 * (sensorRadius (ScreenScale F ε)) ^ 6 ≠ 0) :
    distortPointOTI l1 l2 l3 l4 l5 l6 q1 q2 (ScreenScale F ε) hden_oti
      = ScreenScale F (distortPointCV k1 k2 k3 k4 k5 k6 p1 p2 ε hden_cv) := by
  -- Bridge sensorRadius-squared to the raw x'²+y'² form the pixel theorems use.
  have hr2_cv : (sensorRadius ε) ^ 2 = ε.x ^ 2 + ε.y ^ 2 := Real.sq_sqrt (by positivity)
  have hr2_oti : (sensorRadius (ScreenScale F ε)) ^ 2
      = (F * ε.x) ^ 2 + (F * ε.y) ^ 2 := by
    show (sensorRadius ⟨F * ε.x, F * ε.y⟩) ^ 2 = (F * ε.x) ^ 2 + (F * ε.y) ^ 2
    exact Real.sq_sqrt (by positivity)
  have hCVx : distortXCV k1 k2 k3 k4 k5 k6 p1 p2 ε hden_cv =
      (1 + k1 * (ε.x ^ 2 + ε.y ^ 2) + k2 * (ε.x ^ 2 + ε.y ^ 2) ^ 2
         + k3 * (ε.x ^ 2 + ε.y ^ 2) ^ 3) /
      (1 + k4 * (ε.x ^ 2 + ε.y ^ 2) + k5 * (ε.x ^ 2 + ε.y ^ 2) ^ 2
         + k6 * (ε.x ^ 2 + ε.y ^ 2) ^ 3) * ε.x
      + 2 * p1 * ε.x * ε.y + p2 * (ε.x ^ 2 + ε.y ^ 2 + 2 * ε.x ^ 2) := by
    simp only [distortXCV]
    rw [show (sensorRadius ε) ^ 4 = ((sensorRadius ε) ^ 2) ^ 2 from by ring,
        show (sensorRadius ε) ^ 6 = ((sensorRadius ε) ^ 2) ^ 3 from by ring, hr2_cv]
  have hCVy : distortYCV k1 k2 k3 k4 k5 k6 p1 p2 ε hden_cv =
      (1 + k1 * (ε.x ^ 2 + ε.y ^ 2) + k2 * (ε.x ^ 2 + ε.y ^ 2) ^ 2
         + k3 * (ε.x ^ 2 + ε.y ^ 2) ^ 3) /
      (1 + k4 * (ε.x ^ 2 + ε.y ^ 2) + k5 * (ε.x ^ 2 + ε.y ^ 2) ^ 2
         + k6 * (ε.x ^ 2 + ε.y ^ 2) ^ 3) * ε.y
      + p1 * (ε.x ^ 2 + ε.y ^ 2 + 2 * ε.y ^ 2) + 2 * p2 * ε.x * ε.y := by
    simp only [distortYCV]
    rw [show (sensorRadius ε) ^ 4 = ((sensorRadius ε) ^ 2) ^ 2 from by ring,
        show (sensorRadius ε) ^ 6 = ((sensorRadius ε) ^ 2) ^ 3 from by ring, hr2_cv]
  have hOTIx : distortXOTI l1 l2 l3 l4 l5 l6 q1 q2 (ScreenScale F ε) hden_oti =
      (1 + l1 * ((F * ε.x) ^ 2 + (F * ε.y) ^ 2)
         + l3 * ((F * ε.x) ^ 2 + (F * ε.y) ^ 2) ^ 2
         + l5 * ((F * ε.x) ^ 2 + (F * ε.y) ^ 2) ^ 3) /
      (1 + l2 * ((F * ε.x) ^ 2 + (F * ε.y) ^ 2)
         + l4 * ((F * ε.x) ^ 2 + (F * ε.y) ^ 2) ^ 2
         + l6 * ((F * ε.x) ^ 2 + (F * ε.y) ^ 2) ^ 3) * (F * ε.x)
      + 2 * q1 * (F * ε.x) * (F * ε.y)
      + q2 * ((F * ε.x) ^ 2 + (F * ε.y) ^ 2 + 2 * (F * ε.x) ^ 2) := by
    simp only [distortXOTI]
    rw [show (sensorRadius (ScreenScale F ε)) ^ 4 = ((sensorRadius (ScreenScale F ε)) ^ 2) ^ 2
          from by ring,
        show (sensorRadius (ScreenScale F ε)) ^ 6 = ((sensorRadius (ScreenScale F ε)) ^ 2) ^ 3
          from by ring,
        hr2_oti]
    simp only [ScreenScale]
  have hOTIy : distortYOTI l1 l2 l3 l4 l5 l6 q1 q2 (ScreenScale F ε) hden_oti =
      (1 + l1 * ((F * ε.x) ^ 2 + (F * ε.y) ^ 2)
         + l3 * ((F * ε.x) ^ 2 + (F * ε.y) ^ 2) ^ 2
         + l5 * ((F * ε.x) ^ 2 + (F * ε.y) ^ 2) ^ 3) /
      (1 + l2 * ((F * ε.x) ^ 2 + (F * ε.y) ^ 2)
         + l4 * ((F * ε.x) ^ 2 + (F * ε.y) ^ 2) ^ 2
         + l6 * ((F * ε.x) ^ 2 + (F * ε.y) ^ 2) ^ 3) * (F * ε.y)
      + q1 * ((F * ε.x) ^ 2 + (F * ε.y) ^ 2 + 2 * (F * ε.y) ^ 2)
      + 2 * q2 * (F * ε.x) * (F * ε.y) := by
    simp only [distortYOTI]
    rw [show (sensorRadius (ScreenScale F ε)) ^ 4 = ((sensorRadius (ScreenScale F ε)) ^ 2) ^ 2
          from by ring,
        show (sensorRadius (ScreenScale F ε)) ^ 6 = ((sensorRadius (ScreenScale F ε)) ^ 2) ^ 3
          from by ring,
        hr2_oti]
    simp only [ScreenScale]
  -- Instantiate the two already-proved pixel theorems at this point.
  have hpixel_x := opencv_openlensio_full_pipeline_pixel_corrected
      k1 k2 k3 k4 k5 k6 p1 p2 l1 l2 l3 l4 l5 l6 q1 q2
      fx cx ws w F ΔPx hw hws hF hF_pos hl1 hl3 hl5 hl2 hl4 hl6 hq1 hq2
      hF_eq_x hΔPx hden ε.x ε.y
  have hpixel_y := opencv_openlensio_full_pipeline_pixel_corrected_y
      k1 k2 k3 k4 k5 k6 p1 p2 l1 l2 l3 l4 l5 l6 q1 q2
      fy cy h_shader h F ΔPy hh hhs hF hl1 hl3 hl5 hl2 hl4 hl6 hq1 hq2
      hF_eq_y hΔPy hden ε.x ε.y
  rw [← hCVx, ← hOTIx] at hpixel_x
  rw [← hCVy, ← hOTIy] at hpixel_y
  -- Unwrap: (ws/w)*ΔPx + ws/2 = cx, so the shared offset cancels.
  have hoff_x : (ws / w) * ΔPx + ws / 2 = cx := by rw [hΔPx]; field_simp [hw, hws]; ring
  have hoff_y : (h_shader / h) * ΔPy + h_shader / 2 = cy := by
    rw [hΔPy]; field_simp [hh, hhs]; ring
  have hwsw : (ws / w) ≠ 0 := div_ne_zero hws hw
  have hhsh : (h_shader / h) ≠ 0 := div_ne_zero hhs hh
  have hscale_x : ws / w * F = fx := by rw [hF_eq_x]; field_simp [hw, hws]
  have hscale_y : h_shader / h * F = fy := by rw [hF_eq_y]; field_simp [hh, hhs]
  apply SensorPoint.ext
  · show distortXOTI l1 l2 l3 l4 l5 l6 q1 q2 (ScreenScale F ε) hden_oti
        = F * distortXCV k1 k2 k3 k4 k5 k6 p1 p2 ε hden_cv
    have key : (ws / w) * distortXOTI l1 l2 l3 l4 l5 l6 q1 q2 (ScreenScale F ε) hden_oti
        = fx * distortXCV k1 k2 k3 k4 k5 k6 p1 p2 ε hden_cv := by
      rw [mul_add] at hpixel_x; linarith [hpixel_x, hoff_x]
    rw [← hscale_x] at key
    have key2 : (ws / w) * distortXOTI l1 l2 l3 l4 l5 l6 q1 q2 (ScreenScale F ε) hden_oti
        = (ws / w) * (F * distortXCV k1 k2 k3 k4 k5 k6 p1 p2 ε hden_cv) := by
      rw [key]; ring
    exact mul_left_cancel₀ hwsw key2
  · show distortYOTI l1 l2 l3 l4 l5 l6 q1 q2 (ScreenScale F ε) hden_oti
        = F * distortYCV k1 k2 k3 k4 k5 k6 p1 p2 ε hden_cv
    have key : (h_shader / h) * distortYOTI l1 l2 l3 l4 l5 l6 q1 q2 (ScreenScale F ε) hden_oti
        = fy * distortYCV k1 k2 k3 k4 k5 k6 p1 p2 ε hden_cv := by
      rw [mul_add] at hpixel_y; linarith [hpixel_y, hoff_y]
    rw [← hscale_y] at key
    have key2 : (h_shader / h) * distortYOTI l1 l2 l3 l4 l5 l6 q1 q2 (ScreenScale F ε) hden_oti
        = (h_shader / h) * (F * distortYCV k1 k2 k3 k4 k5 k6 p1 p2 ε hden_cv) := by
      rw [key]; ring
    exact mul_left_cancel₀ hhsh key2
