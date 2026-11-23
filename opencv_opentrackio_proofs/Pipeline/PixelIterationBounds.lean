/-
  Pipeline/PixelIterationBounds.lean

  Converts the normalised-coordinate iteration error bounds of
  Pipeline/IterationErrorBounds.lean into PIXEL units via the actual camera
  intrinsics `fx` (the pinhole relation `pixel = fx·normalised + cx` is
  affine, so a normalised-coordinate error `ε` corresponds to EXACTLY
  `fx·ε` of pixel error — no approximation), and instantiates the result for
  real calibrations at a SPECIFIC, concrete iteration count `N`, each
  verified by `norm_num` on the exact rational coefficients.

  MATHEMATICAL vs FLOATING-POINT, stated once, binding throughout this file
  (see audit/CERTIFIED_NUMERICAL_INVERSION.md §2 for the full account): every
  theorem here is an EXACT-REAL statement about the iteration
  `z_{n+1} = y - Pert θ z_n` evaluated with infinite precision. It says
  nothing about what happens when this same recurrence is evaluated in
  IEEE-754 double precision — rounding error accumulation over N iterations
  is a SEPARATE, unaddressed question (audit/REAL_CALIBRATION_VALIDATION.md
  §5 already found floating-point evaluation of this exact recurrence stays
  accurate to machine epsilon over ~100 iterations for these same real
  calibrations, but that is a numerical observation, not something proved
  here).

  Does not modify any existing file, weaken any existing theorem, or
  introduce axioms.
-/

import Pipeline.IterationErrorBounds
import Pipeline.RealCalibrationExamplesImproved
import Pipeline.RealCalibrationKinectImproved

/-─────────────────────────────────────────────────────────────────────────────
  TUM fr1 at R = 7/10 (fx = 517.306408), N = 17: < 0.001 px.
─────────────────────────────────────────────────────────────────────────────-/

theorem fr1_pixel_error_bound_N17 (y : ℂ) (hy : ‖y‖
    + MPertTightPos (262383/1000000) (-953104/1000000) (1163314/1000000)
        (-5358/1000000) (2628/1000000) (7/10) ≤ (7/10 : ℝ)) :
    (517306408/1000000 : ℝ)
      * ‖(inverseStepRTight (262383/1000000) (-953104/1000000) (1163314/1000000)
            (-5358/1000000) (2628/1000000) y)^[17] y
          - RDistInvTight (262383/1000000) (-953104/1000000) (1163314/1000000)
              (-5358/1000000) (2628/1000000) (7/10) (by norm_num)
              fr1_disc_h fr1_disc_g fr1_disc_psi fr1_k3_pos fr1_contraction_improved y‖
      < 1/1000 := by
  have hb := RDist_iteration_error_bound_tight_pos (262383/1000000) (-953104/1000000) (1163314/1000000)
    (-5358/1000000) (2628/1000000) (7/10) (by norm_num)
    fr1_disc_h fr1_disc_g fr1_disc_psi fr1_k3_pos fr1_contraction_improved y hy 17
  have hfx : (0:ℝ) ≤ 517306408/1000000 := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hb hfx
  have hnum : (517306408/1000000 : ℝ)
      * (MPertTightPos (262383/1000000) (-953104/1000000) (1163314/1000000)
            (-5358/1000000) (2628/1000000) (7/10)
          * (LPertTightPos (262383/1000000) (-953104/1000000) (1163314/1000000)
              (-5358/1000000) (2628/1000000) (7/10)) ^ 17
          / (1 - LPertTightPos (262383/1000000) (-953104/1000000) (1163314/1000000)
              (-5358/1000000) (2628/1000000) (7/10))) < 1/1000 := by
    unfold MPertTightPos LPertTightPos RfacDevUBTightPos RfacLTightPos M L
    norm_num
  linarith [hmul, hnum]

/-─────────────────────────────────────────────────────────────────────────────
  TUM fr2 at R = 3/4 (fx = 520.908620), N = 26: < 0.001 px.
─────────────────────────────────────────────────────────────────────────────-/

theorem fr2_pixel_error_bound_N26 (y : ℂ) (hy : ‖y‖
    + MPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000)
        (-3257/1000000) (-105/1000000) (3/4) ≤ (3/4 : ℝ)) :
    (520908620/1000000 : ℝ)
      * ‖(inverseStepRTight (231222/1000000) (-784899/1000000) (917205/1000000)
            (-3257/1000000) (-105/1000000) y)^[26] y
          - RDistInvTight (231222/1000000) (-784899/1000000) (917205/1000000)
              (-3257/1000000) (-105/1000000) (3/4) (by norm_num)
              fr2_disc_h fr2_disc_g fr2_disc_psi fr2_k3_pos fr2_contraction_improved y‖
      < 1/1000 := by
  have hb := RDist_iteration_error_bound_tight_pos (231222/1000000) (-784899/1000000) (917205/1000000)
    (-3257/1000000) (-105/1000000) (3/4) (by norm_num)
    fr2_disc_h fr2_disc_g fr2_disc_psi fr2_k3_pos fr2_contraction_improved y hy 26
  have hfx : (0:ℝ) ≤ 520908620/1000000 := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hb hfx
  have hnum : (520908620/1000000 : ℝ)
      * (MPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000)
            (-3257/1000000) (-105/1000000) (3/4)
          * (LPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000)
              (-3257/1000000) (-105/1000000) (3/4)) ^ 26
          / (1 - LPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000)
              (-3257/1000000) (-105/1000000) (3/4))) < 1/1000 := by
    unfold MPertTightPos LPertTightPos RfacDevUBTightPos RfacLTightPos M L
    norm_num
  linarith [hmul, hnum]

/-─────────────────────────────────────────────────────────────────────────────
  Azure Kinect DK at R = 2/5 (fx = 606.908447265625), N = 59: < 0.001 px.
─────────────────────────────────────────────────────────────────────────────-/

theorem kinect_pixel_error_bound_N59 (y : ℂ) (hy : ‖y‖
    + MPertTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
        (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
        ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
        (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5) ≤ (2/5 : ℝ)) :
    (606908447265625/1000000000000 : ℝ)
      * ‖(inverseStepRTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
            (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
            ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
            (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) y)^[59] y
          - RDistInvTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
              (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
              ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
              (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5) (by norm_num)
              kinect_ha1 kinect_hmono1_3 kinect_hmono1_4 kinect_hc1 kinect_hge2_1
              kinect_ha4 kinect_hmono4_3 kinect_hmono4_4 kinect_hc4 kinect_hge2_4
              kinect_hsafe kinect_hcontract y‖
      < 1/1000 := by
  have hb := RDist_iteration_error_bound_tight_neg ((-946766696870327)/6250000000000000)
    ((-470049524307251)/200000000000000) (859809398651123/500000000000000)
    ((-26617521047592133)/100000000000000000) ((-427781867980957)/200000000000000)
    (1612900972366333/1000000000000000) (2856750215869397/2500000000000000000)
    ((-4758566792588681)/20000000000000000000) (2/5) (by norm_num)
    kinect_ha1 kinect_hmono1_3 kinect_hmono1_4 kinect_hc1 kinect_hge2_1
    kinect_ha4 kinect_hmono4_3 kinect_hmono4_4 kinect_hc4 kinect_hge2_4
    kinect_hsafe kinect_hcontract y hy 59
  have hfx : (0:ℝ) ≤ 606908447265625/1000000000000 := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hb hfx
  have hnum : (606908447265625/1000000000000 : ℝ)
      * (MPertTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
            (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
            ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
            (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5)
          * (LPertTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
              (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
              ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
              (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5)) ^ 59
          / (1 - LPertTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
              (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
              ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
              (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5))) < 1/1000 := by
    simp only [MPertTightNeg, LPertTightNeg, RfacDevUBTightNeg, RfacLTightNeg, MtightNeg, LtightNeg, LtightNegU,
      denomLBTightNeg, M, L]
    norm_num
  linarith [hmul, hnum]
