/-
  Pipeline/PixelAccuracy2D.lean

  Corrects a genuine gap in Pipeline/PixelIterationBounds.lean: the theorems
  there (`fr1_pixel_error_bound_N17`, `fr2_pixel_error_bound_N26`,
  `kinect_pixel_error_bound_N59`) bound `fx · ‖Δ‖` (normalised-coordinate
  error scaled by the HORIZONTAL focal length alone). Since the true 2D pixel
  distance after converting BOTH coordinates is
  `√((fx·Δx)² + (fy·Δy)²)` — and `fx ≠ fy` for all three real cameras — this
  is a valid bound on the true 2D pixel distance ONLY when `fx ≥ fy` (then
  `√((fx·Δx)²+(fy·Δy)²) ≤ √((fx·Δx)²+(fx·Δy)²) = fx·‖Δ‖`). That holds for
  TUM fr1 (fx=517.306408 > fy=516.469215) and Azure Kinect DK
  (fx=606.908447... > fy=606.661376...), so those two existing theorems
  ALREADY are valid 2D-pixel-distance bounds — but NOT for TUM fr2, where
  `fy=521.007327 > fx=520.908620` (fy is the larger one). The original
  `fr2_pixel_error_bound_N26` is a true statement about `fx·‖Δ‖`, but that
  quantity is NOT, by itself, a rigorous upper bound on the true 2D pixel
  distance for fr2 — see audit/PIXEL_ACCURACY_DOMAIN_AUDIT.md §1 for the
  full account.

  FIX: the general, always-valid bound is `max(fx,fy) · ‖Δ‖` (never `fx`
  alone, regardless of which of fx,fy is larger). This file proves that
  general fact once (`pixel_dist2D_le_max_mul_norm`) and applies it to all
  three real calibrations, giving honest, dimensionally-correct 2D-pixel-
  distance guarantees — not merely restating the single-axis `fx·‖Δ‖` bound
  under a "2D" label.

  Does NOT modify or weaken Pipeline/PixelIterationBounds.lean's existing
  theorems (they remain true statements about `fx·‖Δ‖`, which for fr1/Kinect
  already equals the 2D bound derived here) — this file only ADDS the
  explicit, general 2D-distance machinery and its three instantiations, and
  clarifies which of the originals were already sufficient.

  Reuses, unchanged: `RDist_iteration_error_bound_tight_pos`/`_neg`
  (Pipeline/IterationErrorBounds.lean) — no new Banach/Lipschitz/contraction
  fact is proved; only the pixel-space geometry is corrected.

  No axioms, no `sorry`.
-/

import Pipeline.IterationErrorBounds
import Pipeline.PixelIterationBounds
import Pipeline.RealCalibrationExamplesImproved
import Pipeline.RealCalibrationKinectImproved

/-─────────────────────────────────────────────────────────────────────────────
  General lemma: the true 2D pixel distance `√((fx·dx)²+(fy·dy)²)` is bounded
  by `max(fx,fy) · √(dx²+dy²)` — regardless of which of `fx,fy` is larger.
  Pure algebra (squares, `max`), no calculus.
─────────────────────────────────────────────────────────────────────────────-/

theorem pixel_dist2D_le_max_mul_norm (fx fy dx dy : ℝ) (hfx : 0 ≤ fx) (hfy : 0 ≤ fy) :
    Real.sqrt ((fx * dx) ^ 2 + (fy * dy) ^ 2) ≤ max fx fy * Real.sqrt (dx ^ 2 + dy ^ 2) := by
  have hmaxnn : 0 ≤ max fx fy := le_trans hfx (le_max_left _ _)
  rw [show max fx fy * Real.sqrt (dx ^ 2 + dy ^ 2) = Real.sqrt ((max fx fy) ^ 2 * (dx ^ 2 + dy ^ 2)) from by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hmaxnn]]
  apply Real.sqrt_le_sqrt
  have h1 : (fx * dx) ^ 2 ≤ (max fx fy) ^ 2 * dx ^ 2 := by
    have hle : fx ≤ max fx fy := le_max_left _ _
    nlinarith [sq_nonneg dx, mul_le_mul_of_nonneg_right hle (sq_nonneg dx), sq_nonneg (fx - max fx fy)]
  have h2 : (fy * dy) ^ 2 ≤ (max fx fy) ^ 2 * dy ^ 2 := by
    have hle : fy ≤ max fx fy := le_max_right _ _
    nlinarith [sq_nonneg dy, mul_le_mul_of_nonneg_right hle (sq_nonneg dy), sq_nonneg (fy - max fx fy)]
  nlinarith [h1, h2]

theorem complex_norm_eq_sqrt_re_im_sq (z : ℂ) : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]; ring_nf

/-─────────────────────────────────────────────────────────────────────────────
  TUM fr1 (fx=517.306408 > fy=516.469215 — fx WAS already the max, so this
  is the SAME numeric bound as `fr1_pixel_error_bound_N17`, now stated
  honestly as a genuine 2D pixel distance).
─────────────────────────────────────────────────────────────────────────────-/

theorem fr1_pixel_dist2D_bound_N17 (y : ℂ) (hy : ‖y‖
    + MPertTightPos (262383/1000000) (-953104/1000000) (1163314/1000000)
        (-5358/1000000) (2628/1000000) (7/10) ≤ (7/10 : ℝ)) :
    Real.sqrt
      (((517306408/1000000 : ℝ) * ((inverseStepRTight (262383/1000000) (-953104/1000000) (1163314/1000000)
            (-5358/1000000) (2628/1000000) y)^[17] y
          - RDistInvTight (262383/1000000) (-953104/1000000) (1163314/1000000)
              (-5358/1000000) (2628/1000000) (7/10) (by norm_num)
              fr1_disc_h fr1_disc_g fr1_disc_psi fr1_k3_pos fr1_contraction_improved y).re) ^ 2
        + ((516469215/1000000 : ℝ) * ((inverseStepRTight (262383/1000000) (-953104/1000000) (1163314/1000000)
            (-5358/1000000) (2628/1000000) y)^[17] y
          - RDistInvTight (262383/1000000) (-953104/1000000) (1163314/1000000)
              (-5358/1000000) (2628/1000000) (7/10) (by norm_num)
              fr1_disc_h fr1_disc_g fr1_disc_psi fr1_k3_pos fr1_contraction_improved y).im) ^ 2)
      < 1/1000 := by
  set Δ := (inverseStepRTight (262383/1000000) (-953104/1000000) (1163314/1000000)
      (-5358/1000000) (2628/1000000) y)^[17] y
      - RDistInvTight (262383/1000000) (-953104/1000000) (1163314/1000000)
          (-5358/1000000) (2628/1000000) (7/10) (by norm_num)
          fr1_disc_h fr1_disc_g fr1_disc_psi fr1_k3_pos fr1_contraction_improved y with hΔ
  have hbase := fr1_pixel_error_bound_N17 y hy
  have h2d := pixel_dist2D_le_max_mul_norm (517306408/1000000) (516469215/1000000) Δ.re Δ.im
    (by norm_num) (by norm_num)
  rw [← complex_norm_eq_sqrt_re_im_sq] at h2d
  have hmax : max (517306408/1000000 : ℝ) (516469215/1000000) = 517306408/1000000 := by norm_num
  rw [hmax] at h2d
  calc Real.sqrt (((517306408/1000000 : ℝ) * Δ.re) ^ 2 + ((516469215/1000000 : ℝ) * Δ.im) ^ 2)
      ≤ (517306408/1000000 : ℝ) * ‖Δ‖ := h2d
    _ < 1/1000 := hbase

/-─────────────────────────────────────────────────────────────────────────────
  TUM fr2 — THE CORRECTED CASE (fy=521.007327 > fx=520.908620: fy, not fx,
  is the larger focal length; `fx·‖Δ‖` alone does not rigorously bound the
  true 2D pixel distance here — this is where the fix is load-bearing, not
  cosmetic).
─────────────────────────────────────────────────────────────────────────────-/

theorem fr2_pixel_dist2D_bound_N26 (y : ℂ) (hy : ‖y‖
    + MPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000)
        (-3257/1000000) (-105/1000000) (3/4) ≤ (3/4 : ℝ)) :
    Real.sqrt
      (((520908620/1000000 : ℝ) * ((inverseStepRTight (231222/1000000) (-784899/1000000) (917205/1000000)
            (-3257/1000000) (-105/1000000) y)^[26] y
          - RDistInvTight (231222/1000000) (-784899/1000000) (917205/1000000)
              (-3257/1000000) (-105/1000000) (3/4) (by norm_num)
              fr2_disc_h fr2_disc_g fr2_disc_psi fr2_k3_pos fr2_contraction_improved y).re) ^ 2
        + ((521007327/1000000 : ℝ) * ((inverseStepRTight (231222/1000000) (-784899/1000000) (917205/1000000)
            (-3257/1000000) (-105/1000000) y)^[26] y
          - RDistInvTight (231222/1000000) (-784899/1000000) (917205/1000000)
              (-3257/1000000) (-105/1000000) (3/4) (by norm_num)
              fr2_disc_h fr2_disc_g fr2_disc_psi fr2_k3_pos fr2_contraction_improved y).im) ^ 2)
      < 1/1000 := by
  set Δ := (inverseStepRTight (231222/1000000) (-784899/1000000) (917205/1000000)
      (-3257/1000000) (-105/1000000) y)^[26] y
      - RDistInvTight (231222/1000000) (-784899/1000000) (917205/1000000)
          (-3257/1000000) (-105/1000000) (3/4) (by norm_num)
          fr2_disc_h fr2_disc_g fr2_disc_psi fr2_k3_pos fr2_contraction_improved y with hΔ
  have hbase := RDist_iteration_error_bound_tight_pos (231222/1000000) (-784899/1000000) (917205/1000000)
    (-3257/1000000) (-105/1000000) (3/4) (by norm_num)
    fr2_disc_h fr2_disc_g fr2_disc_psi fr2_k3_pos fr2_contraction_improved y hy 26
  have h2d := pixel_dist2D_le_max_mul_norm (520908620/1000000) (521007327/1000000) Δ.re Δ.im
    (by norm_num) (by norm_num)
  rw [← complex_norm_eq_sqrt_re_im_sq] at h2d
  have hmax : max (520908620/1000000 : ℝ) (521007327/1000000) = 521007327/1000000 := by norm_num
  rw [hmax] at h2d
  have hfy : (0:ℝ) ≤ 521007327/1000000 := by norm_num
  have hnum : (521007327/1000000 : ℝ)
      * (MPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000)
            (-3257/1000000) (-105/1000000) (3/4)
          * (LPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000)
              (-3257/1000000) (-105/1000000) (3/4)) ^ 26
          / (1 - LPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000)
              (-3257/1000000) (-105/1000000) (3/4))) < 1/1000 := by
    unfold MPertTightPos LPertTightPos RfacDevUBTightPos RfacLTightPos M L
    norm_num
  calc Real.sqrt (((520908620/1000000 : ℝ) * Δ.re) ^ 2 + ((521007327/1000000 : ℝ) * Δ.im) ^ 2)
      ≤ (521007327/1000000 : ℝ) * ‖Δ‖ := h2d
    _ ≤ (521007327/1000000 : ℝ)
        * (MPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000)
              (-3257/1000000) (-105/1000000) (3/4)
            * (LPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000)
                (-3257/1000000) (-105/1000000) (3/4)) ^ 26
            / (1 - LPertTightPos (231222/1000000) (-784899/1000000) (917205/1000000)
                (-3257/1000000) (-105/1000000) (3/4))) :=
        mul_le_mul_of_nonneg_left hbase hfy
    _ < 1/1000 := hnum

/-─────────────────────────────────────────────────────────────────────────────
  Azure Kinect DK (fx=606.908447265625 > fy=606.661376953125 — fx WAS
  already the max, same numeric bound as `kinect_pixel_error_bound_N59`, now
  stated honestly as a genuine 2D pixel distance).
─────────────────────────────────────────────────────────────────────────────-/

theorem kinect_pixel_dist2D_bound_N59 (y : ℂ) (hy : ‖y‖
    + MPertTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
        (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
        ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
        (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5) ≤ (2/5 : ℝ)) :
    Real.sqrt
      (((606908447265625/1000000000000 : ℝ) * ((inverseStepRTightNeg ((-946766696870327)/6250000000000000)
            ((-470049524307251)/200000000000000) (859809398651123/500000000000000)
            ((-26617521047592133)/100000000000000000) ((-427781867980957)/200000000000000)
            (1612900972366333/1000000000000000) (2856750215869397/2500000000000000000)
            ((-4758566792588681)/20000000000000000000) y)^[59] y
          - RDistInvTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
              (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
              ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
              (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5) (by norm_num)
              kinect_ha1 kinect_hmono1_3 kinect_hmono1_4 kinect_hc1 kinect_hge2_1
              kinect_ha4 kinect_hmono4_3 kinect_hmono4_4 kinect_hc4 kinect_hge2_4
              kinect_hsafe kinect_hcontract y).re) ^ 2
        + ((606661376953125/1000000000000 : ℝ) * ((inverseStepRTightNeg ((-946766696870327)/6250000000000000)
            ((-470049524307251)/200000000000000) (859809398651123/500000000000000)
            ((-26617521047592133)/100000000000000000) ((-427781867980957)/200000000000000)
            (1612900972366333/1000000000000000) (2856750215869397/2500000000000000000)
            ((-4758566792588681)/20000000000000000000) y)^[59] y
          - RDistInvTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
              (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
              ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
              (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5) (by norm_num)
              kinect_ha1 kinect_hmono1_3 kinect_hmono1_4 kinect_hc1 kinect_hge2_1
              kinect_ha4 kinect_hmono4_3 kinect_hmono4_4 kinect_hc4 kinect_hge2_4
              kinect_hsafe kinect_hcontract y).im) ^ 2)
      < 1/1000 := by
  set Δ := (inverseStepRTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
      (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
      ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
      (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) y)^[59] y
      - RDistInvTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
          (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
          ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
          (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5) (by norm_num)
          kinect_ha1 kinect_hmono1_3 kinect_hmono1_4 kinect_hc1 kinect_hge2_1
          kinect_ha4 kinect_hmono4_3 kinect_hmono4_4 kinect_hc4 kinect_hge2_4
          kinect_hsafe kinect_hcontract y with hΔ
  have hbase := kinect_pixel_error_bound_N59 y hy
  have h2d := pixel_dist2D_le_max_mul_norm (606908447265625/1000000000000) (606661376953125/1000000000000)
    Δ.re Δ.im (by norm_num) (by norm_num)
  rw [← complex_norm_eq_sqrt_re_im_sq] at h2d
  have hmax : max (606908447265625/1000000000000 : ℝ) (606661376953125/1000000000000)
      = 606908447265625/1000000000000 := by norm_num
  rw [hmax] at h2d
  calc Real.sqrt (((606908447265625/1000000000000 : ℝ) * Δ.re) ^ 2
        + ((606661376953125/1000000000000 : ℝ) * Δ.im) ^ 2)
      ≤ (606908447265625/1000000000000 : ℝ) * ‖Δ‖ := h2d
    _ < 1/1000 := hbase
