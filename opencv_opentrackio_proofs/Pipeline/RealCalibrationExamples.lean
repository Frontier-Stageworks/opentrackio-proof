/-
  Pipeline/RealCalibrationExamples.lean

  A genuine, independently-sourced, real-world camera calibration exercising
  the full bounded-domain-invertibility chain (RationalRadialBounds.lean →
  RationalDistortionBounds.lean → RationalDistortionInjectivity.lean →
  RationalDistortionBridge.lean), as opposed to the hand-picked toy
  coefficients of RationalDistortionExamples.lean.

  SOURCE: TUM RGB-D SLAM Benchmark ("Freiburg 1" / fr1 camera), as published
  in ORB-SLAM2's calibration file
  https://github.com/raulmur/ORB_SLAM2/blob/master/Examples/Monocular/TUM1.yaml
  (fetched and quoted verbatim 2026-11-20). This file's camera intrinsics
  match Table II of Sturm et al., "A Benchmark for the Evaluation of RGB-D
  SLAM Systems," IROS 2012 (fx=517.3, fy=516.5, cx=318.6, cy=255.3, reported
  there to one decimal place; ORB-SLAM2's YAML carries the full-precision
  calibration output). Image resolution 640×480 (full sensor resolution,
  Sturm et al. §IV). Published distortion coefficients (OpenCV's own 5-term
  model: k4=k5=k6=0, i.e. a non-rational denominator — see
  audit/REAL_CALIBRATION_VALIDATION.md §2 for why no publicly traceable real
  calibration with a genuine nonzero rational denominator giving a provable
  region was found suitable for a Lean proof of this complexity; the Azure
  Kinect DK rational-model calibration analyzed numerically there IS a real
  counter-example with k4,k5,k6 ≠ 0, but its bounds are evaluated only in
  Python, not proved in Lean — see that document for the full account):

    Camera.k1: 0.262383
    Camera.k2: -0.953104
    Camera.p1: -0.005358
    Camera.p2: 0.002628
    Camera.k3: 1.163314

  These six decimal digits are the FULL PRECISION of the published value;
  represented below as exact rationals over 1000000 — this is not a rounding
  or approximation of some other "true" value, it is the published
  calibration output itself, represented exactly.

  Radius: R = 1/2 (normalised sensor coordinates — the model's own unit,
  matching distortXCV/distortYCV's `sensorRadius`). This is comfortably
  inside the numerically-computed certified bound for this calibration
  (R* ≈ 0.558, see audit/REAL_CALIBRATION_VALIDATION.md §2) — R=1/2 is
  chosen for a clean rational with ample slack for `norm_num`, not pushed to
  the boundary. The disk ‖z‖≤1/2 covers roughly half the physical image's
  surface area (exact figures and the image-vs-disk geometry are in the
  audit document, which is Python-computed, not Lean-proved).

  Does not modify any established definition. Reuses
  RCoeffs/denomMargin/LPert/RDist_inverse_invOn/CVmap_inverse_invOn exactly
  as RationalDistortionExamples.lean does; no new machinery.
-/

import Pipeline.RationalDistortionBridge
import Pipeline.InverseConjugacyApplication

/-─────────────────────────────────────────────────────────────────────────────
  θ_fr1 — the TUM fr1 calibration, exact rationals, k4=k5=k6=0 (the published
  calibration used OpenCV's 5-coefficient model, not the 8-coefficient
  rational model — a genuine, real-world fact about how this camera was
  calibrated, not a simplification introduced here).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def θ_fr1 : RCoeffs :=
  ⟨262383/1000000, -953104/1000000, 1163314/1000000, 0, 0, 0, -5358/1000000, 2628/1000000⟩

/-─────────────────────────────────────────────────────────────────────────────
  Global denominator-nonzero hypothesis: trivial here (k4=k5=k6=0 means the
  denominator is literally the constant 1 for every input, not merely
  positive on some disk).
─────────────────────────────────────────────────────────────────────────────-/

theorem hden_fr1 : ∀ x' y' : ℝ,
    1 + (0 : ℝ) * (x' ^ 2 + y' ^ 2) + (0 : ℝ) * (x' ^ 2 + y' ^ 2) ^ 2
      + (0 : ℝ) * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0 := by
  intro x' y'; norm_num

/-─────────────────────────────────────────────────────────────────────────────
  Task item 6 (non-degeneracy guard): explicit check that the radial
  numerator and denominator polynomials do NOT cancel — i.e. this is not a
  repeat of the k1=k4 identity-collapse bug corrected in
  RationalDistortionExamples.lean. Evaluated at r²=1/4 (the radius used
  below): numerator = 1 + k1/4 + k2/16 + k3/64, denominator = 1 (since
  k4=k5=k6=0). These are shown unequal by direct rational arithmetic.
─────────────────────────────────────────────────────────────────────────────-/

theorem fr1_radial_noncancellation :
    (1 + (262383/1000000 : ℝ) * (1/4) + (-953104/1000000 : ℝ) * (1/4) ^ 2
       + (1163314/1000000 : ℝ) * (1/4) ^ 3)
      ≠ (1 + (0 : ℝ) * (1/4) + (0 : ℝ) * (1/4) ^ 2 + (0 : ℝ) * (1/4) ^ 3) := by
  norm_num

/-─────────────────────────────────────────────────────────────────────────────
  Denominator safety and contraction, at R = 1/2.
─────────────────────────────────────────────────────────────────────────────-/

theorem fr1_denom_safe : denomMargin θ_fr1 (1/2) < 1 := by
  simp only [denomMargin, Mrad, denCoeffs, θ_fr1]
  norm_num

theorem fr1_contraction : LPert θ_fr1 (1/2) < 1 := by
  simp only [LPert, RfacDevUB, RfacL, denomLB, denomMargin, Mrad, Lrad, NnumUB, DdenUB,
    numCoeffs, denCoeffs, L, tangCoeffs, θ_fr1]
  norm_num

/-─────────────────────────────────────────────────────────────────────────────
  Non-identity witness: the point (1/2, 0) is genuinely moved — not merely
  "nonzero coefficients were supplied," a computed, machine-checked
  inequality of actual output values. R(1/4) = 1 + k1/4+k2/16+k3/64 ≠ 1
  (fr1_radial_noncancellation above), so the x-output differs from 1/2 by
  that same nonzero factor applied to 1/2, plus a small tangential term.
─────────────────────────────────────────────────────────────────────────────-/

theorem fr1_not_identity :
    CVmap (262383/1000000) (-953104/1000000) (1163314/1000000) 0 0 0
      (-5358/1000000) (2628/1000000) hden_fr1 (⟨1/2, 0⟩ : SensorPoint)
      ≠ (⟨1/2, 0⟩ : SensorPoint) := by
  intro h
  have hx : (CVmap (262383/1000000) (-953104/1000000) (1163314/1000000) 0 0 0
      (-5358/1000000) (2628/1000000) hden_fr1 (⟨1/2, 0⟩ : SensorPoint)).x
      = (1/2 : ℝ) := by rw [h]
  have hr : sensorRadius (⟨1/2, 0⟩ : SensorPoint) = 1/2 := by
    unfold sensorRadius
    rw [show ((1/2 : ℝ)) ^ 2 + (0 : ℝ) ^ 2 = (1/2 : ℝ) ^ 2 from by ring]
    exact Real.sqrt_sq (by norm_num)
  simp only [CVmap, distortPointCV, distortXCV, hr] at hx
  norm_num at hx

/-─────────────────────────────────────────────────────────────────────────────
  The main result: genuine existence/uniqueness of the inverse on an
  explicit, checkable, positive-radius certified region, for a REAL,
  independently-sourced calibration (not a hand-picked toy example) —
  obtained by direct reuse of RDist_inverse_invOn /
  CVmap_inverse_invOn, no new proof machinery.
─────────────────────────────────────────────────────────────────────────────-/

theorem fr1_invertible :
    Set.InvOn (RDistInv θ_fr1 (1/2) (by norm_num) fr1_denom_safe fr1_contraction) (RDist θ_fr1)
      {z : ℂ | ‖z‖ ≤ 1/2 ∧ ‖RDist θ_fr1 z‖ + MPert θ_fr1 (1/2) ≤ 1/2}
      {y : ℂ | ‖y‖ + MPert θ_fr1 (1/2) ≤ 1/2} :=
  RDist_inverse_invOn θ_fr1 (1/2) (by norm_num) fr1_denom_safe fr1_contraction

theorem fr1_CVmap_invertible :
    Set.InvOn
      (toComplexEquiv.symm ∘
        RDistInv (RCoeffsOf (262383/1000000) (-953104/1000000) (1163314/1000000) 0 0 0
          (-5358/1000000) (2628/1000000)) (1/2) (by norm_num) fr1_denom_safe fr1_contraction
        ∘ toComplexEquiv)
      (CVmap (262383/1000000) (-953104/1000000) (1163314/1000000) 0 0 0
        (-5358/1000000) (2628/1000000) hden_fr1)
      (toComplexEquiv.symm ''
        {z : ℂ | ‖z‖ ≤ 1/2 ∧ ‖RDist
            (RCoeffsOf (262383/1000000) (-953104/1000000) (1163314/1000000) 0 0 0
              (-5358/1000000) (2628/1000000)) z‖
          + MPert (RCoeffsOf (262383/1000000) (-953104/1000000) (1163314/1000000) 0 0 0
              (-5358/1000000) (2628/1000000)) (1/2) ≤ 1/2})
      (toComplexEquiv.symm ''
        {y : ℂ | ‖y‖ + MPert
            (RCoeffsOf (262383/1000000) (-953104/1000000) (1163314/1000000) 0 0 0
              (-5358/1000000) (2628/1000000)) (1/2) ≤ 1/2}) :=
  CVmap_inverse_invOn (262383/1000000) (-953104/1000000) (1163314/1000000) 0 0 0
    (-5358/1000000) (2628/1000000) hden_fr1 (1/2) (by norm_num) fr1_denom_safe fr1_contraction
