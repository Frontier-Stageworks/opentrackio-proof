/-
  LensSemantics.lean — SLICE-OL-01

  Defines the validated semantic types for the OpenLensIO lens model.
  These types represent the mathematical content of a decoded Lens value
  after the semantic bridge (SemanticBridge.lean) has validated the inputs.

  All fields are over ℝ. Positivity and domain invariants live in
  ValidLensSemantics. Denominator nonzero is deferred to SLICE-OL-05
  (RadialPolynomial) per AMB-OL-007.

  Paper reference: OpenLensIO v1.0.1, §1.3 (parameter list), §1.5 (ΔC, ΔP).

  NAMING NOTE (Gate 1 audit): The k-coefficient naming follows the OpenLensIO
  paper §4.1 Eq (17): k1,k3,k5 are numerator; k2,k4,k6 are denominator
  (alternating). This differs from DistortionConversion.lean which uses
  k1–k3 for OpenCV numerator and k4–k6 for OpenCV denominator. Do not
  conflate the two conventions.
-/

import CoordinateTypes

/-─────────────────────────────────────────────────────────────────────────────
  RadialCoefficients

  The six coefficients of the rational radial distortion polynomial R (Eq 17).
  Naming: k1,k3,k5 are numerator terms; k2,k4,k6 are denominator terms.
  R = (1 + k1·r² + k3·r⁴ + k5·r⁶) / (1 + k2·r² + k4·r⁴ + k6·r⁶)

  All values are over ℝ; they originate from JSON number strings parsed
  by the semantic bridge. The denominator nonzero condition is a separate
  predicate introduced in SLICE-OL-05 (AMB-OL-007).
─────────────────────────────────────────────────────────────────────────────-/

structure RadialCoefficients where
  k1 : ℝ
  k2 : ℝ
  k3 : ℝ
  k4 : ℝ
  k5 : ℝ
  k6 : ℝ

/-─────────────────────────────────────────────────────────────────────────────
  TangentialCoefficients

  The Brown-Conrady decentering coefficients p1, p2 (§4.1 Eq 16).
  These are optional in the OpenLensIO parameter list (§1.3). When absent
  from Lens.distortion.tangential, the bridge substitutes zero (AMB-OL-013).
─────────────────────────────────────────────────────────────────────────────-/

structure TangentialCoefficients where
  p1 : ℝ
  p2 : ℝ

def TangentialCoefficients.zero : TangentialCoefficients := ⟨0, 0⟩

/-─────────────────────────────────────────────────────────────────────────────
  LensSemantics

  The validated semantic content of a decoded Lens, ready for use in the
  mathematical distortion and projection models.

  Fields:
    focalLength  — F in mm (§1.1); must be positive (ValidLensSemantics)
    radial       — k1..k6 (§4.1 Eq 17)
    tangential   — p1, p2 (§4.1 Eq 16); zero if absent from parser
    distCentre   — ΔC in mm (§1.5); offset of distortion centre
    perspOffset  — ΔP in mm (§1.5); perspective offset
─────────────────────────────────────────────────────────────────────────────-/

structure LensSemantics where
  focalLength  : ℝ
  radial       : RadialCoefficients
  tangential   : TangentialCoefficients
  distCentre   : SensorPoint
  perspOffset  : SensorPoint

/-─────────────────────────────────────────────────────────────────────────────
  ValidLensSemantics

  Semantic domain requirements for a LensSemantics value.

  focalLength_pos: F > 0 required by §1.1 (focal length is a positive length).

  Denominator nonzero is intentionally absent here. It is a per-point
  condition (depends on the input radius r) and is introduced as an
  explicit hypothesis in SLICE-OL-05 (AMB-OL-007).
─────────────────────────────────────────────────────────────────────────────-/

def ValidLensSemantics (l : LensSemantics) : Prop :=
  0 < l.focalLength
