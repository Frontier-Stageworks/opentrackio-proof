/-
  Pipeline/RealCalibrationKinectImproved.lean

  The first Lean-verified example for the Azure Kinect DK calibration
  (audit/REAL_CALIBRATION_VALIDATION.md, audit/IMPROVED_REAL_CALIBRATION_BOUNDS.md),
  using its ACTUAL, genuinely nonzero rational-model denominator coefficients
  (k4,k5,k6 ≠ 0 — not the trivial-denominator case of
  Pipeline/RealCalibrationExamplesImproved.lean), via the "monotone-negative"
  tightening of Pipeline/TightBoundsWithDenominator.lean.

  SOURCE: Azure Kinect DK RGB camera factory calibration, as published (full
  `rational_polynomial` model, 8 coefficients) in
  https://raw.githubusercontent.com/TINY-KE/active_object_slam/master/config/kinectdk_lj.yaml
  (fetched and quoted verbatim 2026-11-20 — see
  audit/REAL_CALIBRATION_VALIDATION.md §1a for full provenance). Coefficients
  represented as exact rationals matching the published float64 decimal
  strings exactly (not rounded further).

  SCOPE, STATED HONESTLY: this proves genuine existence/uniqueness of the
  inverse at the ℂ/`RDist` level — i.e. for the actual rational Brown-Conrady
  map abstractly, on an explicit certified disk. It does NOT bridge to
  `CVmap`/`SensorPoint` (unlike Pipeline/RealCalibrationExamplesImproved.lean's
  fr1/fr2 examples): doing so would additionally require a GLOBAL
  denominator-nonvanishing fact `∀ x' y' : ℝ, 1+k4(x'²+y'²)+k5(...)²+k6(...)³≠0`
  for ALL real inputs, not just within the certified disk. This is TRUE for
  these coefficients (the denominator's global minimum, found numerically via
  the actual critical point of the cubic-in-r² polynomial, is ≈0.1995 at
  r≈0.970 — never reaching zero), but proving that global fact in Lean would
  require a genuinely different argument (the full cubic-minimum calculation,
  valid for ALL r, not just the monotone-decreasing-on-a-bounded-interval
  argument `cubic_tight_neg`/`quad_mono_nonpos` give) that was not built in
  this pass. This is reported as an explicit, bounded scope limitation, not
  elided.

  Does not modify any existing file, weaken any existing theorem, or
  introduce axioms.
-/

import Pipeline.TightBoundsWithDenominator

noncomputable def θ_kinect : RCoeffs :=
  ⟨(-946766696870327)/6250000000000000, (-470049524307251)/200000000000000, 859809398651123/500000000000000,
   (-26617521047592133)/100000000000000000, (-427781867980957)/200000000000000, 1612900972366333/1000000000000000,
   2856750215869397/2500000000000000000, (-4758566792588681)/20000000000000000000⟩

/-─────────────────────────────────────────────────────────────────────────────
  All side conditions, verified exactly at R = 2/5 (well under the numerically
  estimated full-tight R* ≈ 0.4158 — see
  audit/IMPROVED_REAL_CALIBRATION_BOUNDS.md §4, chosen with headroom).
─────────────────────────────────────────────────────────────────────────────-/

theorem kinect_ha1 : ((-946766696870327)/6250000000000000 : ℝ) ≤ 0 := by norm_num
theorem kinect_hmono1_3 :
    ((-470049524307251)/200000000000000 : ℝ) + 3 * (859809398651123/500000000000000) * (2/5:ℝ) ^ 2 ≤ 0 := by
  norm_num
theorem kinect_hmono1_4 :
    ((-470049524307251)/200000000000000 : ℝ) + 4 * (859809398651123/500000000000000) * (2/5:ℝ) ^ 2 ≤ 0 := by
  norm_num
theorem kinect_hc1 : (0:ℝ) < 859809398651123/500000000000000 := by norm_num
theorem kinect_hge2_1 : (-2:ℝ) ≤ ((-946766696870327)/6250000000000000) * (2/5:ℝ) ^ 2
    + ((-470049524307251)/200000000000000) * (2/5:ℝ) ^ 4 + (859809398651123/500000000000000) * (2/5:ℝ) ^ 6 := by
  norm_num

theorem kinect_ha4 : ((-26617521047592133)/100000000000000000 : ℝ) ≤ 0 := by norm_num
theorem kinect_hmono4_3 :
    ((-427781867980957)/200000000000000 : ℝ) + 3 * (1612900972366333/1000000000000000) * (2/5:ℝ) ^ 2 ≤ 0 := by
  norm_num
theorem kinect_hmono4_4 :
    ((-427781867980957)/200000000000000 : ℝ) + 4 * (1612900972366333/1000000000000000) * (2/5:ℝ) ^ 2 ≤ 0 := by
  norm_num
theorem kinect_hc4 : (0:ℝ) < 1612900972366333/1000000000000000 := by norm_num
theorem kinect_hge2_4 : (-2:ℝ) ≤ ((-26617521047592133)/100000000000000000) * (2/5:ℝ) ^ 2
    + ((-427781867980957)/200000000000000) * (2/5:ℝ) ^ 4 + (1612900972366333/1000000000000000) * (2/5:ℝ) ^ 6 := by
  norm_num

theorem kinect_hsafe : MtightNeg ((-26617521047592133)/100000000000000000) ((-427781867980957)/200000000000000)
    (1612900972366333/1000000000000000) (2/5) < 1 := by
  unfold MtightNeg; norm_num

theorem kinect_hcontract :
    LPertTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
      (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
      ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
      (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5) < 1 := by
  simp only [LPertTightNeg, RfacDevUBTightNeg, RfacLTightNeg, MtightNeg, LtightNeg, LtightNegU,
    denomLBTightNeg, L]
  norm_num

/-- Explicit non-identity witness: `RDist θ_kinect (2/5) ≠ 2/5` — the radial
factor at `r²=4/25` genuinely moves the point (computed, not assumed). -/
theorem kinect_not_identity : RDist θ_kinect (2/5 : ℂ) ≠ (2/5 : ℂ) := by
  intro h
  have hre : (RDist θ_kinect (2/5 : ℂ)).re = (2/5 : ℝ) := by rw [h]; norm_num
  have heq : (RDist θ_kinect (2/5 : ℂ)).re
      = (Rfac θ_kinect (2/5 : ℂ) : ℝ) * (2/5 : ℂ).re
        + (radial (tangCoeffs θ_kinect) (2/5 : ℂ) * (2/5 : ℂ).re
            + 2 * (tangCoeffs θ_kinect).p1 * (2/5 : ℂ).re * (2/5 : ℂ).im
            + (tangCoeffs θ_kinect).p2 * (Complex.normSq (2/5 : ℂ) + 2 * (2/5 : ℂ).re ^ 2)) := by
    unfold RDist
    rw [Complex.add_re, Complex.real_smul, Complex.mul_re]
    show _ = _ + (Tang θ_kinect (2/5 : ℂ)).re
    congr 1
    simp
  rw [heq] at hre
  have hRfac : Rfac θ_kinect (2/5 : ℂ)
      = (1 + ((-946766696870327)/6250000000000000 : ℝ) * (4/25) + ((-470049524307251)/200000000000000) * (4/25)^2
            + (859809398651123/500000000000000) * (4/25)^3)
        / (1 + ((-26617521047592133)/100000000000000000 : ℝ) * (4/25) + ((-427781867980957)/200000000000000) * (4/25)^2
            + (1612900972366333/1000000000000000) * (4/25)^3) := by
    show Nnum θ_kinect (2/5 : ℂ) / Dden θ_kinect (2/5 : ℂ) = _
    unfold Nnum Dden radial numCoeffs denCoeffs θ_kinect
    norm_num [Complex.normSq_apply]
  rw [hRfac] at hre
  simp only [tangCoeffs, θ_kinect, radial, Complex.normSq_apply] at hre
  norm_num at hre

/-─────────────────────────────────────────────────────────────────────────────
  The main result: genuine existence/uniqueness of the inverse of the actual
  rational (numerator AND denominator both genuinely nonzero, real-data)
  Brown-Conrady map, on an explicit certified disk — the first time this
  repository has proved this at a Lean level for a calibration with a real
  nonzero rational denominator, at R = 2/5.
─────────────────────────────────────────────────────────────────────────────-/

theorem kinect_invertible :
    Set.InvOn
      (RDistInvTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
        (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
        ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
        (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5) (by norm_num)
        kinect_ha1 kinect_hmono1_3 kinect_hmono1_4 kinect_hc1 kinect_hge2_1
        kinect_ha4 kinect_hmono4_3 kinect_hmono4_4 kinect_hc4 kinect_hge2_4
        kinect_hsafe kinect_hcontract)
      (RDist θ_kinect)
      {z : ℂ | ‖z‖ ≤ (2/5 : ℝ) ∧ ‖RDist θ_kinect z‖
        + MPertTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
            (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
            ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
            (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5) ≤ (2/5 : ℝ)}
      {y : ℂ | ‖y‖ + MPertTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
            (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
            ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
            (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5) ≤ (2/5 : ℝ)} :=
  RDist_inverse_invOn_tight_neg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
    (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
    ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
    (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5) (by norm_num)
    kinect_ha1 kinect_hmono1_3 kinect_hmono1_4 kinect_hc1 kinect_hge2_1
    kinect_ha4 kinect_hmono4_3 kinect_hmono4_4 kinect_hc4 kinect_hge2_4
    kinect_hsafe kinect_hcontract
