/-
  Pipeline/PixelIffCorrected.lean

  Companion to `Pipeline/PixelIff.lean`. That file proves
  `opencv_openlensio_full_pipeline_pixel_iff` under the paper's stated
  tangential conversion `q1 = p1/F², q2 = p2/F²`, and correctly finds that full
  pixel agreement then requires the extra condition `ws/w = fx`. Nothing in
  that file (or `PixelIffHelpers.lean`, `PixelSufficiency.lean`,
  `DistortionConversion.lean`) is modified here.

  This file proves the pixel-level consequence of the corrected tangential
  conversion `q1 = p1/F, q2 = p2/F` derived in `DistortionConversionCorrected.lean`:
  under that correction, full pixel-x agreement holds UNCONDITIONALLY — no
  `ws/w = fx` side condition survives, and no `p1 ≠ 0 ∨ p2 ≠ 0` hypothesis is
  needed either.

  Why: substituting q1 = p1/F, q2 = p2/F into the OTI tangential term gives
  exactly `F · T_cv(x', y')`, i.e. the tangential term now carries the same
  single F factor that the radial term already carries through its `(F·x')`
  multiplier. Combined with `(ws/w)·F = fx` (from `hF_eq`) and the (already
  unconditional) principal-point cancellation, both pipelines reduce to the
  syntactically identical expression `fx·(R_cv·x' + T_cv) + cx`. The naive
  analog of the existing iff — `pixel_eq ↔ ws/w = fx` — is therefore FALSE
  under the corrected hypotheses; `physical_pixel_agreement_scale_independent_example`
  below exhibits a concrete counterexample (pixel agreement with `ws/w ≠ fx`).

  See `docs/laps/tangential-conversion-physical-fix/` for the full derivation,
  statement audit, and ambiguity register.

  CLAIM SCOPE (see the per-theorem comments below for detail): both theorems
  in this file are same-direction (U→D) coordinate-conjugacy results between
  OpenCV's forward-distortion formula and the same formula shape applied to
  converted OpenTrackIO coefficients — not claims about native OpenLensIO
  D→U undistortion consumption of those coefficients, which the OpenTrackIO
  schema's `distortion.model` default ("Brown-Conrady D-U") would actually
  invoke. See `docs/specification-questions.md` SQ-CV-07.
-/

import DistortionConversion

/-─────────────────────────────────────────────────────────────────────────────
  opencv_openlensio_full_pipeline_pixel_corrected

  Given the radial parameter conversions (unchanged from the paper) and the
  CORRECTED tangential conversion q1 = p1/F, q2 = p2/F, the full pixel
  x-outputs agree for EVERY normalised input point — unconditionally.

  CLAIM SCOPE — read before citing this theorem: this is a same-direction
  coordinate-conjugacy result, not a claim about native OpenLensIO
  undistortion. Both sides of the equation apply the SAME undistorted→distorted
  formula shape (OpenCV's own convention — matching `distortXCV`/`distortYCV`
  in `OpenCVModel.lean`, and what the OpenTrackIO schema's
  `distortion.model = "Brown-Conrady U-D"` designation would mean): the LHS is
  the CV formula at (x', y'); the RHS is the SAME formula shape (via the
  converted l/q coefficients) at the scaled screen point (F·x', F·y'). The
  theorem says these two U→D evaluations agree, related by the coordinate
  scaling S_F(x, y) = (F·x, F·y).

  This is NOT a claim that the converted l/q coefficients, if consumed by a
  real OpenTrackIO implementation as NATIVE OpenLensIO U (the D→U direction —
  distorted input, undistorted output — which is the OpenTrackIO JSON
  schema's default for `distortion.model` when that field is omitted; see
  `docs/specification-questions.md` SQ-CV-07), would reproduce correct
  undistortion. That D→U claim is separate, harder, and NOT addressed here:
  it would require either an exact inverse-function bridge between this
  proved U→D conjugacy and the D→U direction, or a bounded-error
  approximation theorem — neither of which exists in this repository. See
  `docs/limitations.md` and `Pipeline/README.md`'s "Claim scope" section.
─────────────────────────────────────────────────────────────────────────────-/

theorem opencv_openlensio_full_pipeline_pixel_corrected
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fx cx ws w F ΔPx : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0) (hF : F ≠ 0) (hF_pos : 0 < F)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hq1 : q1 = p1 / F) (hq2 : q2 = p2 / F)                              -- CORRECTED
    (hF_eq : F = (w / ws) * fx) (hΔPx : ΔPx = (w / ws) * (cx - ws / 2))
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
  -- fx ≠ 0, derived from hF ≠ 0 and hF_eq (no hscale needed: F = (w/ws)*fx ≠ 0
  -- with w/ws ≠ 0 forces fx ≠ 0).
  have hfx : fx ≠ 0 := by
    have hF' : (w / ws) * fx ≠ 0 := hF_eq ▸ hF
    exact right_ne_zero_of_mul hF'
  -- Radial numerator/denominator equality: OTI at (F·x', F·y') = CV at (x', y').
  -- Identical to the corresponding `have`s in `opencv_openlensio_full_pipeline_pixel_sufficiency`;
  -- does not depend on q1, q2, so unaffected by the tangential fix.
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
  rw [h_num, h_den, hq1, hq2, hΔPx, hF_eq]
  field_simp [hw, hws, hfx, hden_xy]
  ring

/-─────────────────────────────────────────────────────────────────────────────
  physical_pixel_agreement_scale_independent_example

  Concrete numeric witness confirming the residual condition genuinely
  collapses to "no condition at all" rather than merely "not yet proved":
  under the corrected conversions, pixel agreement holds even when
  ws/w ≠ fx. This mechanically refutes the naive analog of
  `opencv_openlensio_full_pipeline_pixel_iff` (`pixel_eq ↔ ws/w = fx`) ported
  verbatim to the corrected hypotheses.

  Witness: fx = 1, ws = 2, w = 1  ⟹  F = (w/ws)·fx = 1/2, ws/w = 2 ≠ fx = 1.
  Pure tangential lens (p1 = 1, p2 = 0, all radial coefficients zero) so the
  denominator is identically 1 ≠ 0.

  CLAIM SCOPE: inherits the same-direction coordinate-conjugacy scope of
  `opencv_openlensio_full_pipeline_pixel_corrected` above — the pixel equation
  witnessed here is the U→D conjugacy, not a claim about native OpenLensIO
  (D→U) undistortion consumption of the converted coefficients.
─────────────────────────────────────────────────────────────────────────────-/

theorem physical_pixel_agreement_scale_independent_example :
    ∃ k1 k2 k3 k4 k5 k6 p1 p2 l1 l2 l3 l4 l5 l6 q1 q2
      fx cx ws w F ΔPx : ℝ,
      w ≠ 0 ∧ ws ≠ 0 ∧ F ≠ 0 ∧ 0 < F ∧
      l1 = k1 / F ^ 2 ∧ l3 = k2 / F ^ 4 ∧ l5 = k3 / F ^ 6 ∧
      l2 = k4 / F ^ 2 ∧ l4 = k5 / F ^ 4 ∧ l6 = k6 / F ^ 6 ∧
      q1 = p1 / F ∧ q2 = p2 / F ∧
      F = (w / ws) * fx ∧ ΔPx = (w / ws) * (cx - ws / 2) ∧
      (∀ x' y' : ℝ,
          1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
            + k6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0) ∧
      ws / w ≠ fx ∧
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
        + ws / 2) := by
  refine ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0,
    1, 0, 2, 1, 1 / 2, -(1 / 2),
    by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num,
    by norm_num, by norm_num,
    ?_, by norm_num, ?_⟩
  · intro x' y'; norm_num
  · exact opencv_openlensio_full_pipeline_pixel_corrected
      0 0 0 0 0 0 1 0 0 0 0 0 0 0 2 0
      1 0 2 1 (1 / 2) (-(1 / 2))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro x' y'; norm_num)
