/-
  Pipeline/OpenTrackIOModel.lean

  OpenTrackIO forward-distortion definitions in screen-space coordinate space.

  DIRECTION NOTE: these definitions compute the SAME multiply-add SHAPE as
  OpenCV's distortXCV/distortYCV (OpenCVModel.lean), here applied to the
  OpenTrackIO-side coefficients l1..l6, q1, q2 instead of OpenCV's k1..k6, p1,
  p2. This is the forward "distortion function" the conversion paper calls D
  ("formerly named D", the inverse of OpenLensIO's native undistortion
  function U) — NOT OpenLensIO's native U itself. OpenLensIO's native U is
  `undistortPoint` in openlensio_semantics/DistortionModel.lean, operating on
  a DIFFERENT coefficient structure (RadialCoefficients/TangentialCoefficients,
  OpenLensIO's own alternating k-convention, mm units) — do not conflate the
  two. See docs/specification-questions.md SQ-CV-07 and Pipeline/README.md's
  "Claim scope" section.

  No theorem in this repository currently names the OpenTrackIO-side forward
  map used inline in Pipeline/PixelIffCorrected.lean's
  `opencv_openlensio_full_pipeline_pixel_corrected` (confirmed: that theorem's
  statement never calls a named function for the OTI side — it is fully
  inlined over raw reals). Naming it here lets
  Pipeline/ForwardConjugacy.lean state a genuine two-dimensional, composed-
  function conjugacy `distortPointOTI = S_F ∘ distortPointCV ∘ S_F⁻¹` instead
  of only a per-coordinate real-number identity.
-/

import Pipeline.OpenCVModel

/-─────────────────────────────────────────────────────────────────────────────
  distortXOTI

  The x-component of OpenTrackIO's forward distortion at a screen-space
  UNDISTORTED point ε (same formula shape as distortXCV; see that file for
  the per-term derivation). l1,l3,l5 = radial numerator; l2,l4,l6 = radial
  denominator (matching the convention already used throughout
  DistortionConversion.lean / Pipeline/PixelIffCorrected.lean).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def distortXOTI
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (ε : SensorPoint)
    (_ : 1 + l2 * (sensorRadius ε) ^ 2 + l4 * (sensorRadius ε) ^ 4
           + l6 * (sensorRadius ε) ^ 6 ≠ 0) : ℝ :=
  let r := sensorRadius ε
  (1 + l1 * r ^ 2 + l3 * r ^ 4 + l5 * r ^ 6) /
  (1 + l2 * r ^ 2 + l4 * r ^ 4 + l6 * r ^ 6) * ε.x
  + 2 * q1 * ε.x * ε.y + q2 * (r ^ 2 + 2 * ε.x ^ 2)

/-─────────────────────────────────────────────────────────────────────────────
  distortYOTI

  The y-component of OpenTrackIO's forward distortion. Symmetric to
  distortXOTI with q1/q2 roles swapped, matching distortYCV's δy shape:
  δy := q1·(r² + 2·ε.y²) + 2·q2·ε.x·ε.y
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def distortYOTI
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (ε : SensorPoint)
    (_ : 1 + l2 * (sensorRadius ε) ^ 2 + l4 * (sensorRadius ε) ^ 4
           + l6 * (sensorRadius ε) ^ 6 ≠ 0) : ℝ :=
  let r := sensorRadius ε
  (1 + l1 * r ^ 2 + l3 * r ^ 4 + l5 * r ^ 6) /
  (1 + l2 * r ^ 2 + l4 * r ^ 4 + l6 * r ^ 6) * ε.y
  + q1 * (r ^ 2 + 2 * ε.y ^ 2) + 2 * q2 * ε.x * ε.y

/-─────────────────────────────────────────────────────────────────────────────
  distortPointOTI

  The full OpenTrackIO forward-distortion map D_oti : SensorPoint → SensorPoint
  (undistorted screen point in, distorted screen point out). Packages
  distortXOTI and distortYOTI into a SensorPoint, mirroring distortPointCV.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def distortPointOTI
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (ε : SensorPoint)
    (hden : 1 + l2 * (sensorRadius ε) ^ 2 + l4 * (sensorRadius ε) ^ 4
              + l6 * (sensorRadius ε) ^ 6 ≠ 0) : SensorPoint :=
  ⟨distortXOTI l1 l2 l3 l4 l5 l6 q1 q2 ε hden,
   distortYOTI l1 l2 l3 l4 l5 l6 q1 q2 ε hden⟩
