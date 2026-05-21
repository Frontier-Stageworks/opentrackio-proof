/-
  FovModel.lean — SLICE-OL-11

  Defines the FOV-form projection and undistortion equations from OpenLensIO §3:
    Eq (9):  ε'_u = F·[x/z_p, y/z_p]^T           (fovProjectToImage — no ΔP)
    Eq (10): ε'_u = U(ε'_d − ΔC) + ΔC             (fovUndistortFromDistorted — no ΔP)

  The FOV form uses coordinates centred at the optical axis. The projection
  matrix form (Eqs 3, 4) includes ΔP offsets. The two forms are related by
  Eqs (12) and (13): ε_u = ε'_u + ΔP, ε_d = ε'_d + ΔP.

  Theorem: fov_undistort_eq
    Structural consistency of Eq (10) with Eq (4): when ε_d = ε'_d + ΔP,
    undistortFromDistorted for ε_d equals fovUndistortFromDistorted for ε'_d
    plus ΔP. The load-bearing algebraic step is distortion_center_translation_commutes
    (OL-09), which proves the argument to U is the same in both forms.

  Dropped: fov_projection_translation (true by rfl — trivial definitional tautology).
-/

import ProjectionModel

/-─────────────────────────────────────────────────────────────────────────────
  fovProjectToImage — Eq (9)

  §3: ε'_u = F·[x/z_p, y/z_p]^T  (no ΔP term)
  The FOV form uses coordinates centred at the principal point / optical axis.
  Eq (3) is the projection matrix form: ε_u = F·u + ΔP = fovProjectToImage F u + ΔP.
  The relationship ε_u = ε'_u + ΔP follows from definitions by rfl; no theorem needed.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def fovProjectToImage (F : ℝ) (u : SensorPoint) : SensorPoint :=
  ⟨F * u.x, F * u.y⟩

/-─────────────────────────────────────────────────────────────────────────────
  fovUndistortFromDistorted — Eq (10)

  §3: ε'_u = U(ε'_d − ΔC) + ΔC  (no ΔP terms)
  Eq (4) is the projection matrix form: ε_u = U(ε_d − ΔC − ΔP) + ΔC + ΔP.
  When ε_d = ε'_d + ΔP (Eq 13), the argument to U is the same:
    (ε'_d + ΔP) − ΔC − ΔP = ε'_d − ΔC  (distortion_center_translation_commutes).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def fovUndistortFromDistorted
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε'_d ΔC : SensorPoint)
    (h : denominatorNonzero k (sensorRadius (subSensorPoints ε'_d ΔC))) : SensorPoint :=
  addSensorPoints (undistortPoint k p (subSensorPoints ε'_d ΔC) h) ΔC

/-─────────────────────────────────────────────────────────────────────────────
  fov_undistort_eq

  Structural consistency of Eq (10) with Eq (4) via the ΔP translation:
    undistortFromDistorted for (ε'_d + ΔP) = fovUndistortFromDistorted for ε'_d + ΔP

  The theorem takes two domain hypotheses:
    h  : denominatorNonzero k (sensorRadius (ε'_d − ΔC))
    h' : denominatorNonzero k (sensorRadius ((ε'_d + ΔP) − ΔC − ΔP))
  These are proofs of propositionally-equal (by distortion_center_translation_commutes)
  but definitionally-distinct SensorPoint expressions. Both are needed because
  undistortFromDistorted and fovUndistortFromDistorted are defined with different
  argument forms; the two domain proofs cannot be conflated at the definition level.

  Proof strategy:
    1. `simp only [undistortFromDistorted, fovUndistortFromDistorted]` unfolds both
       definitions, exposing two `undistortPoint` calls at structurally different
       SensorPoint arguments.
    2. `congr 1; congr 1` reduces the goal to showing the two `undistortPoint` calls
       are equal — i.e., that U applied at ε'_d−ΔC with proof h equals U applied at
       (ε'_d+ΔP)−ΔC−ΔP with proof h'.
    3. `undistortPoint_congr` closes this by supplying the SensorPoint equality
       (distortion_center_translation_commutes ε'_d ΔP ΔC) and appealing to Lean 4
       proof irrelevance: both h and h' are proofs of the same Prop after substitution.
─────────────────────────────────────────────────────────────────────────────-/

/-─────────────────────────────────────────────────────────────────────────────
  undistortPoint_congr

  Helper: undistortPoint is equal when the SensorPoint arguments are equal.
  The proof argument h is proof-irrelevant (Prop); `subst` substitutes the
  SensorPoint equality and `rfl` closes by Lean 4 proof irrelevance.

  Role in fov_undistort_eq: allows equating the two undistortPoint calls after
  distortion_center_translation_commutes establishes the SensorPoint argument equality.
─────────────────────────────────────────────────────────────────────────────-/

private lemma undistortPoint_congr
    (k : RadialCoefficients) (p : TangentialCoefficients)
    {ε₁ ε₂ : SensorPoint} (hε : ε₁ = ε₂)
    (h₁ : denominatorNonzero k (sensorRadius ε₁))
    (h₂ : denominatorNonzero k (sensorRadius ε₂)) :
    undistortPoint k p ε₁ h₁ = undistortPoint k p ε₂ h₂ := by
  subst hε; rfl

theorem fov_undistort_eq
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε'_d ΔC ΔP : SensorPoint)
    (h  : denominatorNonzero k (sensorRadius (subSensorPoints ε'_d ΔC)))
    (h' : denominatorNonzero k (sensorRadius (subSensorPoints (subSensorPoints (addSensorPoints ε'_d ΔP) ΔC) ΔP))) :
    undistortFromDistorted k p (addSensorPoints ε'_d ΔP) ΔC ΔP h' =
    addSensorPoints (fovUndistortFromDistorted k p ε'_d ΔC h) ΔP := by
  simp only [undistortFromDistorted, fovUndistortFromDistorted]
  congr 1; congr 1
  exact undistortPoint_congr k p (distortion_center_translation_commutes ε'_d ΔP ΔC) h' h
