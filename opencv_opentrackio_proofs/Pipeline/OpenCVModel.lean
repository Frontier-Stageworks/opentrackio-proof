/-
  Pipeline/OpenCVModel.lean

  OpenCV Brown-Conrady undistortion definitions in normalised coordinate space.

  NAMING NOTE: OpenCV uses k1,k2,k3 (numerator) and k4,k5,k6 (denominator).
  OpenLensIO uses k1,k3,k5 (numerator) and k2,k4,k6 (denominator, alternating).
  These conventions conflict. This file uses OpenCV naming for OpenCV parameters.
  When constructing a RadialCoefficients value from OpenCV params, the field mapping is:
    ⟨cv_k1, cv_k4, cv_k2, cv_k5, cv_k3, cv_k6⟩
  (OTI fields k1,k2,k3,k4,k5,k6 map to OTI-num,OTI-den,OTI-num,OTI-den,OTI-num,OTI-den)
-/

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
