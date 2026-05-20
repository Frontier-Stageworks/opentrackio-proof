/-
  ProjectionModel.lean — SLICE-OL-10

  Defines the projection and undistortion equations from OpenLensIO §2:
    Eq (3): ε_u = F·[x/z_p, y/z_p]^T + ΔP      (projectToImage)
    Eq (4): ε_u = U(ε_d − ΔC − ΔP) + ΔC + ΔP   (undistortFromDistorted)

  Theorem: projection_matrix_undistort_eq
    Structural consistency of Eq (4): removing the ΔC+ΔP offset from
    undistortFromDistorted's output recovers undistortPoint's output.
    ((U(ε_d − ΔC − ΔP) + ΔC + ΔP) − ΔC − ΔP = U(ε_d − ΔC − ΔP))

  Scope limitation: full Eq(3)/Eq(4) consistency (agreeing on corresponding
  inputs) requires the forward distortion model and is deferred to
  OL-DEFER-03 or a future forward-model slice.
-/

import DeltaSemantics
import DistortionModel

/-─────────────────────────────────────────────────────────────────────────────
  CameraPoint

  Alias for SensorPoint used for normalized camera-frame coordinates.
  Both are ℝ × ℝ records; the alias documents the coordinate-space role
  without introducing a new type. (Phantom-type tagging deferred per AMB-OL-004.)
─────────────────────────────────────────────────────────────────────────────-/

abbrev CameraPoint := SensorPoint

/-─────────────────────────────────────────────────────────────────────────────
  projectToImage — Eq (3)

  §2: ε_u = F·[x/z_p, y/z_p]^T + ΔP
  where u = (x_p/z_p, y_p/z_p) are normalized camera-frame coordinates
  (the caller divides by z_p; z_p ≠ 0 is the caller's precondition).
  F > 0 is carried by ValidLensSemantics; callers supply it as a real.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def projectToImage (F : ℝ) (u ΔP : SensorPoint) : SensorPoint :=
  ⟨F * u.x + ΔP.x, F * u.y + ΔP.y⟩

/-─────────────────────────────────────────────────────────────────────────────
  undistortFromDistorted — Eq (4)

  §2: ε_u = U(ε_d − ΔC − ΔP) + ΔC + ΔP

  The argument to U is the distorted coordinate shifted by −(ΔC + ΔP),
  moving it into the distortion-centred coordinate frame. After applying U,
  the result is shifted back by +(ΔC + ΔP).

  The denominatorNonzero precondition is evaluated at the shifted argument
  (ε_d − ΔC − ΔP), not at ε_d itself. Callers must supply evidence that
  the denominator is nonzero at the actual input to U.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def undistortFromDistorted
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε_d ΔC ΔP : SensorPoint)
    (h : denominatorNonzero k (sensorRadius (subSensorPoints (subSensorPoints ε_d ΔC) ΔP))) :
    SensorPoint :=
  addSensorPoints
    (addSensorPoints
      (undistortPoint k p (subSensorPoints (subSensorPoints ε_d ΔC) ΔP) h)
      ΔC)
    ΔP

/-─────────────────────────────────────────────────────────────────────────────
  projection_matrix_undistort_eq

  Algebraic offset-cancellation consistency of Eq (4): removing the ΔC+ΔP
  offset from undistortFromDistorted's output recovers undistortPoint's output.
  Formally: (U(ε_d − ΔC − ΔP) + ΔC + ΔP) − ΔC − ΔP = U(ε_d − ΔC − ΔP),
  i.e., a + b + c − b − c = a, proved by ring after unfolding the definition.

  Scope limitation: this theorem proves algebraic consistency of the Eq(4)
  offset structure (the ΔC+ΔP wrapping/unwrapping cancels), NOT full
  Eq(3)/Eq(4) forward/inverse equivalence. In particular:
    – it does not relate projectToImage (Eq 3) to undistortFromDistorted (Eq 4);
    – it does not prove that U is invertible;
    – it does not prove that the forward distortion model composes correctly.
  Full forward/inverse equivalence requires the forward distortion model,
  deferred to OL-DEFER-03.
─────────────────────────────────────────────────────────────────────────────-/

theorem projection_matrix_undistort_eq
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε_d ΔC ΔP : SensorPoint)
    (h : denominatorNonzero k (sensorRadius (subSensorPoints (subSensorPoints ε_d ΔC) ΔP))) :
    subSensorPoints (subSensorPoints (undistortFromDistorted k p ε_d ΔC ΔP h) ΔC) ΔP =
    undistortPoint k p (subSensorPoints (subSensorPoints ε_d ΔC) ΔP) h := by
  ext <;> simp [undistortFromDistorted, addSensorPoints, subSensorPoints] <;> ring
