/-
  Pipeline/PixelIffCorrectedY.lean

  Y-axis analogue of Pipeline/PixelIffCorrected.lean, under the SAME corrected
  tangential scaling q1 = p1/F, q2 = p2/F investigated there (NOT the
  as-published q1 = p1/F², q2 = p2/F² — see DistortionConversionCorrected.lean
  and docs/specification-questions.md SQ-CV-06). This file does not modify
  PixelIffCorrected.lean, PixelIff.lean, PixelIffHelpers.lean,
  PixelSufficiency.lean, PixelIffY.lean, PixelIffHelpersY.lean, or
  PixelSufficiencyY.lean.

  This is a genuinely new proof obligation: the existing Y-axis work
  (PixelIffY.lean / PixelSufficiencyY.lean / PixelIffHelpersY.lean, all
  committed under docs/laps/y-pixel-equivalence/) mirrors the AS-PUBLISHED
  (q = p/F²) x-axis family only. No file in this repository previously proved
  a y-component pixel identity for the corrected-scaling model.

  Proof technique: identical in structure to
  `opencv_openlensio_full_pipeline_pixel_corrected`'s own proof
  (PixelIffCorrected.lean:100-132) — the radial bridging (`h_num`, `h_den`) is
  symmetric in x'/y' already (stated purely in terms of `(F*x')^2+(F*y')^2`),
  so it is re-derived verbatim rather than imported; the only semantic change
  is the tangential term's p1/p2 role swap, matching `distortYCV`'s δy shape
  (OpenCVModel.lean:59-67) and DistortionConversionCorrected.lean's own
  x/y-symmetric `whole_tangential_field_2d_iff_physical` (lines 115-138, which
  already establishes both the x and y corrected tangential identities at the
  coefficient level — confirming this y-component pixel identity is the
  expected, not a surprising, consequence of substituting `hq1 : q1 = p1/F`,
  `hq2 : q2 = p2/F` directly).
-/

import Pipeline.PixelIffCorrected

/-─────────────────────────────────────────────────────────────────────────────
  opencv_openlensio_full_pipeline_pixel_corrected_y

  Y-axis analogue of opencv_openlensio_full_pipeline_pixel_corrected: given the
  radial conversions (unchanged) and the corrected tangential conversion
  q1 = p1/F, q2 = p2/F, the full pixel y-outputs agree for every normalised
  input point — unconditionally, mirroring the x-result's unconditional
  nature (no h_shader/h = fy side condition survives, same as the x-theorem's
  ws/w = fx side condition not surviving).
─────────────────────────────────────────────────────────────────────────────-/

theorem opencv_openlensio_full_pipeline_pixel_corrected_y
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fy cy h_shader h F ΔPy : ℝ)
    (hh : h ≠ 0) (hhs : h_shader ≠ 0) (hF : F ≠ 0)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hq1 : q1 = p1 / F) (hq2 : q2 = p2 / F)                              -- CORRECTED
    (hF_eq : F = (h / h_shader) * fy) (hΔPy : ΔPy = (h / h_shader) * (cy - h_shader / 2))
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
      -- OpenTrackIO pixel y-output (screen point (F·x', F·y'))
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
  have hfy : fy ≠ 0 := by
    have hF' : (h / h_shader) * fy ≠ 0 := hF_eq ▸ hF
    exact right_ne_zero_of_mul hF'
  -- Radial numerator/denominator equality: OTI at (F·x', F·y') = CV at (x', y').
  -- Symmetric in x'/y'; identical derivation to PixelIffCorrected.lean's h_num/h_den.
  have h_num :
      1 + l1 * ((F * x') ^ 2 + (F * y') ^ 2)
        + l3 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
        + l5 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3 =
      1 + k1 * (x' ^ 2 + y' ^ 2) + k2 * (x' ^ 2 + y' ^ 2) ^ 2
        + k3 * (x' ^ 2 + y' ^ 2) ^ 3 := by
    have hFsq : (F * x') ^ 2 + (F * y') ^ 2 = F ^ 2 * (x' ^ 2 + y' ^ 2) := by ring
    rw [hFsq, hl1, hl3, hl5]; field_simp [hF2, hF4, hF6]
  have h_den :
      1 + l2 * ((F * x') ^ 2 + (F * y') ^ 2)
        + l4 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
        + l6 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3 =
      1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
        + k6 * (x' ^ 2 + y' ^ 2) ^ 3 := by
    have hFsq : (F * x') ^ 2 + (F * y') ^ 2 = F ^ 2 * (x' ^ 2 + y' ^ 2) := by ring
    rw [hFsq, hl2, hl4, hl6]; field_simp [hF2, hF4, hF6]
  rw [h_num, h_den, hq1, hq2, hΔPy, hF_eq]
  field_simp [hh, hhs, hfy, hden_xy]
  ring
