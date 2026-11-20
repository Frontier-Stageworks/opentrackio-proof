/-
  Pipeline/RealCalibrationExamplesImproved.lean

  Re-certifies the TUM fr1/fr2 real calibrations (Pipeline/RealCalibrationExamples.lean,
  audit/REAL_CALIBRATION_VALIDATION.md) using the TIGHTENED bounds of
  Pipeline/TightBoundsNoDenominator.lean (which in turn rest on
  Pipeline/SignedCubicBounds.lean's signed-cubic discriminant argument), at a
  SUBSTANTIALLY LARGER radius than Pipeline/RealCalibrationExamples.lean's
  R=1/2 — exploiting the real coefficients' actual (mixed, partially
  cancelling) signs rather than the crude Mrad/Lrad sum-of-absolute-values
  bound.

  Same exact published coefficients as Pipeline/RealCalibrationExamples.lean
  (ORB-SLAM2's TUM1.yaml/TUM2.yaml, quoting the TUM RGB-D benchmark's own
  calibration output verbatim as exact rationals over 1000000) — no
  recalibration, no new data.

  Improvement (audit/IMPROVED_REAL_CALIBRATION_BOUNDS.md has the full
  derivation and image-coverage numbers): R=1/2 → R=7/10 (fr1), R=3/4 (fr2).

  Does not modify RealCalibrationExamples.lean, RationalDistortionExamples.lean,
  or any other existing file. No axioms, no `sorry`.
-/

import Pipeline.TightBoundsNoDenominator

/-─────────────────────────────────────────────────────────────────────────────
  fr1 at R = 7/10 (up from 1/2 in RealCalibrationExamples.lean).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def θ_fr1_improved : RCoeffs :=
  ⟨262383/1000000, -953104/1000000, 1163314/1000000, 0, 0, 0, -5358/1000000, 2628/1000000⟩

theorem hden_fr1_improved : ∀ x' y' : ℝ,
    1 + (0 : ℝ) * (x' ^ 2 + y' ^ 2) + (0 : ℝ) * (x' ^ 2 + y' ^ 2) ^ 2
      + (0 : ℝ) * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0 := by
  intro x' y'; norm_num

theorem fr1_disc_h : (-953104/1000000 : ℝ) ^ 2 ≤ 4 * (262383/1000000) * (1163314/1000000) := by
  norm_num

theorem fr1_disc_g :
    ((-953104/1000000 : ℝ) + (1163314/1000000) * (7/10 : ℝ) ^ 2) ^ 2
      ≤ 4 * ((262383/1000000 : ℝ) + (-953104/1000000) * (7/10 : ℝ) ^ 2
              + (1163314/1000000) * (7/10 : ℝ) ^ 4) * (1163314/1000000) := by
  norm_num

theorem fr1_disc_psi : (-953104/1000000 : ℝ) ^ 2 ≤ 3 * (262383/1000000) * (1163314/1000000) := by
  norm_num

theorem fr1_k3_pos : (0:ℝ) < 1163314/1000000 := by norm_num

theorem fr1_contraction_improved :
    LPertTightPos (262383/1000000) (-953104/1000000) (1163314/1000000) (-5358/1000000) (2628/1000000) (7/10) < 1 := by
  unfold LPertTightPos RfacDevUBTightPos RfacLTightPos L
  norm_num

/-- Explicit non-identity witness at `(7/10, 0)`, same style as
RealCalibrationExamples.lean's `fr1_not_identity`: the radial factor at
`r²=0.49` is `1+k1·0.49+k2·0.49²+k3·0.49³ ≠ 1`. -/
theorem fr1_not_identity_improved :
    CVmap (262383/1000000) (-953104/1000000) (1163314/1000000) 0 0 0
      (-5358/1000000) (2628/1000000) hden_fr1_improved (⟨7/10, 0⟩ : SensorPoint)
      ≠ (⟨7/10, 0⟩ : SensorPoint) := by
  intro h
  have hx : (CVmap (262383/1000000) (-953104/1000000) (1163314/1000000) 0 0 0
      (-5358/1000000) (2628/1000000) hden_fr1_improved (⟨7/10, 0⟩ : SensorPoint)).x
      = (7/10 : ℝ) := by rw [h]
  have hr : sensorRadius (⟨7/10, 0⟩ : SensorPoint) = 7/10 := by
    unfold sensorRadius
    rw [show ((7/10 : ℝ)) ^ 2 + (0 : ℝ) ^ 2 = (7/10 : ℝ) ^ 2 from by ring]
    exact Real.sqrt_sq (by norm_num)
  simp only [CVmap, distortPointCV, distortXCV, hr] at hx
  norm_num at hx

/-- The main result: genuine existence/uniqueness of the inverse on an
explicit, checkable, positive-radius certified region, at R=7/10 — up from
R=1/2 in RealCalibrationExamples.lean, via the signed-cubic tightening. -/
theorem fr1_CVmap_invertible_improved :
    Set.InvOn
      (toComplexEquiv.symm ∘
        RDistInvTight (262383/1000000) (-953104/1000000) (1163314/1000000)
          (-5358/1000000) (2628/1000000) (7/10) (by norm_num)
          fr1_disc_h fr1_disc_g fr1_disc_psi fr1_k3_pos fr1_contraction_improved
        ∘ toComplexEquiv)
      (CVmap (262383/1000000) (-953104/1000000) (1163314/1000000) 0 0 0
        (-5358/1000000) (2628/1000000) hden_fr1_improved)
      (toComplexEquiv.symm ''
        {z : ℂ | ‖z‖ ≤ (7/10 : ℝ) ∧ ‖RDist θ_fr1_improved z‖
          + MPertTightPos (262383/1000000) (-953104/1000000) (1163314/1000000)
              (-5358/1000000) (2628/1000000) (7/10) ≤ (7/10 : ℝ)})
      (toComplexEquiv.symm ''
        {y : ℂ | ‖y‖ + MPertTightPos (262383/1000000) (-953104/1000000) (1163314/1000000)
              (-5358/1000000) (2628/1000000) (7/10) ≤ (7/10 : ℝ)}) :=
  CVmap_inverse_invOn_tight (262383/1000000) (-953104/1000000) (1163314/1000000)
    (-5358/1000000) (2628/1000000) hden_fr1_improved (7/10) (by norm_num)
    fr1_disc_h fr1_disc_g fr1_disc_psi fr1_k3_pos fr1_contraction_improved

/-─────────────────────────────────────────────────────────────────────────────
  fr2 at R = 3/4 (up from 1/2 in RealCalibrationExamples.lean).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def θ_fr2_improved : RCoeffs :=
  ⟨231222/1000000, -784899/1000000, 917205/1000000, 0, 0, 0, -3257/1000000, -105/1000000⟩

theorem hden_fr2_improved : ∀ x' y' : ℝ,
    1 + (0 : ℝ) * (x' ^ 2 + y' ^ 2) + (0 : ℝ) * (x' ^ 2 + y' ^ 2) ^ 2
      + (0 : ℝ) * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0 := by
  intro x' y'; norm_num

theorem fr2_disc_h : (-784899/1000000 : ℝ) ^ 2 ≤ 4 * (231222/1000000) * (917205/1000000) := by
  norm_num

theorem fr2_disc_g :
    ((-784899/1000000 : ℝ) + (917205/1000000) * (3/4 : ℝ) ^ 2) ^ 2
      ≤ 4 * ((231222/1000000 : ℝ) + (-784899/1000000) * (3/4 : ℝ) ^ 2
              + (917205/1000000) * (3/4 : ℝ) ^ 4) * (917205/1000000) := by
  norm_num

theorem fr2_disc_psi : (-784899/1000000 : ℝ) ^ 2 ≤ 3 * (231222/1000000) * (917205/1000000) := by
  norm_num

theorem fr2_k3_pos : (0:ℝ) < 917205/1000000 := by norm_num

theorem fr2_contraction_improved :
    LPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000) (-3257/1000000) (-105/1000000) (3/4) < 1 := by
  unfold LPertTightPos RfacDevUBTightPos RfacLTightPos L
  norm_num

theorem fr2_not_identity_improved :
    CVmap (231222/1000000) (-784899/1000000) (917205/1000000) 0 0 0
      (-3257/1000000) (-105/1000000) hden_fr2_improved (⟨3/4, 0⟩ : SensorPoint)
      ≠ (⟨3/4, 0⟩ : SensorPoint) := by
  intro h
  have hx : (CVmap (231222/1000000) (-784899/1000000) (917205/1000000) 0 0 0
      (-3257/1000000) (-105/1000000) hden_fr2_improved (⟨3/4, 0⟩ : SensorPoint)).x
      = (3/4 : ℝ) := by rw [h]
  have hr : sensorRadius (⟨3/4, 0⟩ : SensorPoint) = 3/4 := by
    unfold sensorRadius
    rw [show ((3/4 : ℝ)) ^ 2 + (0 : ℝ) ^ 2 = (3/4 : ℝ) ^ 2 from by ring]
    exact Real.sqrt_sq (by norm_num)
  simp only [CVmap, distortPointCV, distortXCV, hr] at hx
  norm_num at hx

theorem fr2_CVmap_invertible_improved :
    Set.InvOn
      (toComplexEquiv.symm ∘
        RDistInvTight (231222/1000000) (-784899/1000000) (917205/1000000)
          (-3257/1000000) (-105/1000000) (3/4) (by norm_num)
          fr2_disc_h fr2_disc_g fr2_disc_psi fr2_k3_pos fr2_contraction_improved
        ∘ toComplexEquiv)
      (CVmap (231222/1000000) (-784899/1000000) (917205/1000000) 0 0 0
        (-3257/1000000) (-105/1000000) hden_fr2_improved)
      (toComplexEquiv.symm ''
        {z : ℂ | ‖z‖ ≤ (3/4 : ℝ) ∧ ‖RDist θ_fr2_improved z‖
          + MPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000)
              (-3257/1000000) (-105/1000000) (3/4) ≤ (3/4 : ℝ)})
      (toComplexEquiv.symm ''
        {y : ℂ | ‖y‖ + MPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000)
              (-3257/1000000) (-105/1000000) (3/4) ≤ (3/4 : ℝ)}) :=
  CVmap_inverse_invOn_tight (231222/1000000) (-784899/1000000) (917205/1000000)
    (-3257/1000000) (-105/1000000) hden_fr2_improved (3/4) (by norm_num)
    fr2_disc_h fr2_disc_g fr2_disc_psi fr2_k3_pos fr2_contraction_improved

/-─────────────────────────────────────────────────────────────────────────────
  fr2 at R = 79/100 — CAPSTONE: the camera's image corners have normalised
  radius ≈0.7870 (fx=520.908620, fy=521.007327, cx=325.141442, cy=249.701764,
  640×480 — audit/REAL_CALIBRATION_VALIDATION.md §2); R=79/100=0.79 EXCEEDS
  this, so the certified injectivity disk provably contains the ENTIRE image
  rectangle — full-image injectivity, not merely "most of the image," for
  this real calibration. See audit/IMPROVED_REAL_CALIBRATION_BOUNDS.md §5 for
  the corner-radius comparison and the resulting buffer/existence coverage
  (computed, not Lean-proved, since it is a statement about the fixed
  physical image rectangle, not a further Lean inequality).
─────────────────────────────────────────────────────────────────────────────-/

theorem fr2_disc_h_capstone : (-784899/1000000 : ℝ) ^ 2 ≤ 4 * (231222/1000000) * (917205/1000000) := by
  norm_num

theorem fr2_disc_g_capstone :
    ((-784899/1000000 : ℝ) + (917205/1000000) * (79/100 : ℝ) ^ 2) ^ 2
      ≤ 4 * ((231222/1000000 : ℝ) + (-784899/1000000) * (79/100 : ℝ) ^ 2
              + (917205/1000000) * (79/100 : ℝ) ^ 4) * (917205/1000000) := by
  norm_num

theorem fr2_disc_psi_capstone : (-784899/1000000 : ℝ) ^ 2 ≤ 3 * (231222/1000000) * (917205/1000000) := by
  norm_num

theorem fr2_contraction_capstone :
    LPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000)
      (-3257/1000000) (-105/1000000) (79/100) < 1 := by
  unfold LPertTightPos RfacDevUBTightPos RfacLTightPos L
  norm_num

theorem fr2_CVmap_invertible_capstone :
    Set.InvOn
      (toComplexEquiv.symm ∘
        RDistInvTight (231222/1000000) (-784899/1000000) (917205/1000000)
          (-3257/1000000) (-105/1000000) (79/100) (by norm_num)
          fr2_disc_h_capstone fr2_disc_g_capstone fr2_disc_psi_capstone fr2_k3_pos fr2_contraction_capstone
        ∘ toComplexEquiv)
      (CVmap (231222/1000000) (-784899/1000000) (917205/1000000) 0 0 0
        (-3257/1000000) (-105/1000000) hden_fr2_improved)
      (toComplexEquiv.symm ''
        {z : ℂ | ‖z‖ ≤ (79/100 : ℝ) ∧ ‖RDist θ_fr2_improved z‖
          + MPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000)
              (-3257/1000000) (-105/1000000) (79/100) ≤ (79/100 : ℝ)})
      (toComplexEquiv.symm ''
        {y : ℂ | ‖y‖ + MPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000)
              (-3257/1000000) (-105/1000000) (79/100) ≤ (79/100 : ℝ)}) :=
  CVmap_inverse_invOn_tight (231222/1000000) (-784899/1000000) (917205/1000000)
    (-3257/1000000) (-105/1000000) hden_fr2_improved (79/100) (by norm_num)
    fr2_disc_h_capstone fr2_disc_g_capstone fr2_disc_psi_capstone fr2_k3_pos fr2_contraction_capstone
