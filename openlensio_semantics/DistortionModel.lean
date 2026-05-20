/-
  DistortionModel.lean — SLICE-OL-07

  Defines the Brown-Conrady undistortion function U(ϵ) in component
  (non-singular) form from OpenLensIO §4.1 Eq (16).

  Design choice (AMB-OL-004): component form used over the diagonal matrix
  form. Both are algebraically equivalent; the component form stays in ℝ
  and lets ring close polynomial identities without matrix infrastructure.

  U_x(ϵ) = R·ϵ_x + 2·p1·ϵ_x·ϵ_y + p2·(r² + 2·ϵ_x²)
  U_y(ϵ) = R·ϵ_y + p1·(r² + 2·ϵ_y²) + 2·p2·ϵ_x·ϵ_y

  where r = sensorRadius ε and R = radialTerm k r h.
-/

import RadialPolynomial

/-─────────────────────────────────────────────────────────────────────────────
  undistortX

  The x-component of U(ϵ) from §4.1 Eq (16).
  h : denominatorNonzero k (sensorRadius ε) is forwarded to radialTerm.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def undistortX
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε : SensorPoint) (h : denominatorNonzero k (sensorRadius ε)) : ℝ :=
  let r := sensorRadius ε
  radialTerm k r h * ε.x + 2 * p.p1 * ε.x * ε.y + p.p2 * (r ^ 2 + 2 * ε.x ^ 2)

/-─────────────────────────────────────────────────────────────────────────────
  undistortY

  The y-component of U(ϵ) from §4.1 Eq (16).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def undistortY
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε : SensorPoint) (h : denominatorNonzero k (sensorRadius ε)) : ℝ :=
  let r := sensorRadius ε
  radialTerm k r h * ε.y + p.p1 * (r ^ 2 + 2 * ε.y ^ 2) + 2 * p.p2 * ε.x * ε.y

/-─────────────────────────────────────────────────────────────────────────────
  undistortPoint

  The full undistortion map U : SensorPoint → SensorPoint from §4.1 Eq (16).
  Packages undistortX and undistortY into a SensorPoint.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def undistortPoint
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε : SensorPoint) (h : denominatorNonzero k (sensorRadius ε)) : SensorPoint :=
  ⟨undistortX k p ε h, undistortY k p ε h⟩
