/-
  CoordinateTypes.lean — SLICE-OL-04

  Defines the 2D screen/sensor coordinate type and the radius function
  for the OpenLensIO image frame (§1.2, §1.1).

  Paper reference: OpenLensIO v1.0.1, §1.1–1.2.
  Image frame: mm units, origin at centre, ϵ_x right, ϵ_y down.

  Design note (AMB-OL-004): SensorPoint is a plain {x y : ℝ} structure.
  Phantom-type coordinate tagging is deferred; the gate-3 representation
  review chose the minimal structure for the first slices.
-/

import Mathlib.Tactic

/-─────────────────────────────────────────────────────────────────────────────
  SensorPoint

  A 2D point in the image/sensor coordinate frame.
  Units: millimetres. Origin at the centre of the active sensor area.
  ϵ_x increases to the right; ϵ_y increases downward (§1.2 Fig 1).
─────────────────────────────────────────────────────────────────────────────-/

@[ext]
structure SensorPoint where
  x : ℝ
  y : ℝ

/-─────────────────────────────────────────────────────────────────────────────
  sensorRadius

  r = √(ϵ_x² + ϵ_y²)  (§1.1, Eq 16/17 preamble).
  Used as the argument to the radial distortion polynomial.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def sensorRadius (p : SensorPoint) : ℝ :=
  Real.sqrt (p.x ^ 2 + p.y ^ 2)

theorem sensorRadius_nonneg (p : SensorPoint) : 0 ≤ sensorRadius p :=
  Real.sqrt_nonneg _
