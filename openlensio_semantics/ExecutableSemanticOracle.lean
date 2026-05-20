/-
  ExecutableSemanticOracle.lean — SLICE-OL-14

  Float-based executable counterparts of the exact-real OpenLensIO definitions.

  ⚠ FLOAT APPROXIMATION ONLY — NOT A PROVED THEOREM ⚠
  This file implements IEEE 754 double-precision approximations of the
  definitions in DistortionModel, ProjectionModel, FovModel, and ShaderCoords.
  No Lean kernel theorem is stated or verified here. Domain validity is checked
  at Float level with an absolute tolerance (1e-10); this is not a formal proof.

  Corresponding exact definitions:
    sensorRadius           → CoordinateTypes.lean (OL-04)
    radialTerm             → RadialPolynomial.lean (OL-05)
    undistortX, undistortY → DistortionModel.lean (OL-07)
    undistortPoint         → DistortionModel.lean (OL-07)
    undistortFromDistorted → ProjectionModel.lean (OL-10)
    fovUndistortFromDistorted → FovModel.lean (OL-11)
    angleOfView, fovAngleFromWidth → AngleOfView.lean (OL-12)
    toShaderCoords, fromShaderCoords → ShaderCoords.lean (OL-13)
-/

/-─────────────────────────────────────────────────────────────────────────────
  Float structures — parallel to exact types
─────────────────────────────────────────────────────────────────────────────-/

structure FloatSensorPoint where
  x : Float
  y : Float
  deriving Repr

structure FloatRadialCoefficients where
  k1 : Float
  k2 : Float
  k3 : Float
  k4 : Float
  k5 : Float
  k6 : Float
  deriving Repr

structure FloatTangentialCoefficients where
  p1 : Float
  p2 : Float
  deriving Repr

/-─────────────────────────────────────────────────────────────────────────────
  sensorRadius_float — parallel to sensorRadius (OL-04)
─────────────────────────────────────────────────────────────────────────────-/

def sensorRadius_float (p : FloatSensorPoint) : Float :=
  Float.sqrt (p.x ^ 2 + p.y ^ 2)

/-─────────────────────────────────────────────────────────────────────────────
  radialTerm_float — parallel to radialTerm (OL-05)

  Returns none if the denominator is within absolute tolerance 1e-10 of zero.
  This is a Float-level domain check, not a formal proof of denominatorNonzero.
─────────────────────────────────────────────────────────────────────────────-/

def radialTerm_float (k : FloatRadialCoefficients) (r : Float) : Option Float :=
  let r2 := r ^ 2
  let r4 := r2 ^ 2
  let r6 := r2 * r4
  let denom := 1 + k.k2 * r2 + k.k4 * r4 + k.k6 * r6
  if denom.abs < 1e-10 then none
  else some ((1 + k.k1 * r2 + k.k3 * r4 + k.k5 * r6) / denom)

/-─────────────────────────────────────────────────────────────────────────────
  undistortX_float, undistortY_float — parallel to component forms (OL-07)

  R is the pre-computed radial term (already checked nonzero by caller).
  Signature differs from exact: takes R : Float instead of h : denominatorNonzero,
  since domain validity is handled by the Option return in radialTerm_float.
─────────────────────────────────────────────────────────────────────────────-/

def undistortX_float (p : FloatTangentialCoefficients)
    (ex ey r R : Float) : Float :=
  R * ex + 2 * p.p1 * ex * ey + p.p2 * (r ^ 2 + 2 * ex ^ 2)

def undistortY_float (p : FloatTangentialCoefficients)
    (ex ey r R : Float) : Float :=
  R * ey + p.p1 * (r ^ 2 + 2 * ey ^ 2) + 2 * p.p2 * ex * ey

/-─────────────────────────────────────────────────────────────────────────────
  undistortPoint_float — parallel to undistortPoint (OL-07)

  Returns none if radialTerm_float detects a near-zero denominator.
─────────────────────────────────────────────────────────────────────────────-/

def undistortPoint_float (k : FloatRadialCoefficients) (p : FloatTangentialCoefficients)
    (ε : FloatSensorPoint) : Option FloatSensorPoint :=
  let r := sensorRadius_float ε
  match radialTerm_float k r with
  | none   => none
  | some R => some ⟨undistortX_float p ε.x ε.y r R, undistortY_float p ε.x ε.y r R⟩

/-─────────────────────────────────────────────────────────────────────────────
  undistortFromDistorted_float — parallel to undistortFromDistorted (OL-10)

  Eq (4): ε_u = U(ε_d − ΔC − ΔP) + ΔC + ΔP
─────────────────────────────────────────────────────────────────────────────-/

def undistortFromDistorted_float (k : FloatRadialCoefficients) (p : FloatTangentialCoefficients)
    (εd ΔC ΔP : FloatSensorPoint) : Option FloatSensorPoint :=
  let shifted : FloatSensorPoint := ⟨εd.x - ΔC.x - ΔP.x, εd.y - ΔC.y - ΔP.y⟩
  match undistortPoint_float k p shifted with
  | none   => none
  | some u => some ⟨u.x + ΔC.x + ΔP.x, u.y + ΔC.y + ΔP.y⟩

/-─────────────────────────────────────────────────────────────────────────────
  fovUndistortFromDistorted_float — parallel to fovUndistortFromDistorted (OL-11)

  Eq (10): ε'_u = U(ε'_d − ΔC) + ΔC  (no ΔP — FOV form)
─────────────────────────────────────────────────────────────────────────────-/

def fovUndistortFromDistorted_float (k : FloatRadialCoefficients) (p : FloatTangentialCoefficients)
    (ε'_d ΔC : FloatSensorPoint) : Option FloatSensorPoint :=
  let shifted : FloatSensorPoint := ⟨ε'_d.x - ΔC.x, ε'_d.y - ΔC.y⟩
  match undistortPoint_float k p shifted with
  | none   => none
  | some u => some ⟨u.x + ΔC.x, u.y + ΔC.y⟩

/-─────────────────────────────────────────────────────────────────────────────
  toShaderCoords_float, fromShaderCoords_float — parallel to OL-13
─────────────────────────────────────────────────────────────────────────────-/

def toShaderCoords_float (w h wshader : Float) (p : FloatSensorPoint) : FloatSensorPoint :=
  ⟨wshader * p.x / w + wshader / 2, wshader * p.y / h + wshader / 2⟩

def fromShaderCoords_float (w h wshader : Float) (q : FloatSensorPoint) : FloatSensorPoint :=
  ⟨w * (q.x - wshader / 2) / wshader, h * (q.y - wshader / 2) / wshader⟩

/-─────────────────────────────────────────────────────────────────────────────
  angleOfView_float, fovAngleFromWidth_float — parallel to OL-12
─────────────────────────────────────────────────────────────────────────────-/

def angleOfView_float (F r_u : Float) : Float :=
  2 * Float.atan (r_u / F)

def fovAngleFromWidth_float (F w : Float) : Float :=
  2 * Float.atan (w / (2 * F))

/-─────────────────────────────────────────────────────────────────────────────
  #eval demonstrations
  These verify the oracle runs. They are not proofs.
─────────────────────────────────────────────────────────────────────────────-/

-- Identity coefficients: all k and p = 0 → U(ε) = ε
-- Expected output: some { x := 1.0, y := 2.0 }
#eval undistortPoint_float
  { k1 := 0, k2 := 0, k3 := 0, k4 := 0, k5 := 0, k6 := 0 }
  { p1 := 0, p2 := 0 }
  { x := 1.0, y := 2.0 }

-- Typical barrel distortion (k1 > 0): point moves outward from centre
-- Expected output: some point with x > 1.0, y > 2.0
#eval undistortPoint_float
  { k1 := 0.1, k2 := 0.0, k3 := 0.0, k4 := 0.0, k5 := 0.0, k6 := 0.0 }
  { p1 := 0.0, p2 := 0.0 }
  { x := 1.0, y := 2.0 }

-- Shader coordinate roundtrip: sensor (5.0, -3.0) mm → shader → back
-- Expected: second component ≈ { x := 5.0, y := -3.0 }
#eval
  let p : FloatSensorPoint := { x := 5.0, y := -3.0 }
  let q := toShaderCoords_float 24.0 13.5 4096.0 p
  let p' := fromShaderCoords_float 24.0 13.5 4096.0 q
  (q, p')

-- FOV angle for a 24mm-wide sensor at 50mm focal length
-- Expected: ≈ 0.466 radians (≈ 26.7°)
#eval angleOfView_float 50.0 12.0
