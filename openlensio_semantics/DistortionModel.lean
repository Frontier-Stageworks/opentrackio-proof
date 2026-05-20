/-
  DistortionModel.lean — SLICE-OL-07 + SLICE-OL-08

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

/-─────────────────────────────────────────────────────────────────────────────
  tangential_zero_coefficients_identity

  With zero tangential coefficients, the x-component of U reduces to R·ϵ_x.
  Stepping stone for brown_conrady_zero_identity.
─────────────────────────────────────────────────────────────────────────────-/

theorem tangential_zero_coefficients_identity
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε : SensorPoint) (h : denominatorNonzero k (sensorRadius ε))
    (hp1 : p.p1 = 0) (hp2 : p.p2 = 0) :
    undistortX k p ε h = radialTerm k (sensorRadius ε) h * ε.x := by
  simp only [undistortX, hp1, hp2, mul_zero, zero_mul, add_zero]

/-─────────────────────────────────────────────────────────────────────────────
  brown_conrady_zero_identity

  When all eight distortion coefficients are zero, U(ϵ) = ϵ.
  Closes the identity proof chain: radial_zero_coefficients_identity (R=1)
  + tangential_zero_coefficients_identity (U_x = R·ϵ_x) → U = id.
─────────────────────────────────────────────────────────────────────────────-/

theorem brown_conrady_zero_identity
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε : SensorPoint) (h : denominatorNonzero k (sensorRadius ε))
    (hk1 : k.k1 = 0) (hk2 : k.k2 = 0) (hk3 : k.k3 = 0)
    (hk4 : k.k4 = 0) (hk5 : k.k5 = 0) (hk6 : k.k6 = 0)
    (hp1 : p.p1 = 0) (hp2 : p.p2 = 0) :
    undistortPoint k p ε h = ε := by
  have hR : radialTerm k (sensorRadius ε) h = 1 :=
    radial_zero_coefficients_identity k (sensorRadius ε) hk1 hk2 hk3 hk4 hk5 hk6 h
  have hX : undistortX k p ε h = ε.x := by
    have htang := tangential_zero_coefficients_identity k p ε h hp1 hp2
    rw [htang, hR, one_mul]
  have hY : undistortY k p ε h = ε.y := by
    simp only [undistortY, hp1, hp2, hR, mul_zero, zero_mul, add_zero, one_mul]
  exact SensorPoint.ext hX hY
