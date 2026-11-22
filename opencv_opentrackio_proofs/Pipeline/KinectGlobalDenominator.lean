/-
  Pipeline/KinectGlobalDenominator.lean

  Proves that Azure Kinect DK's ACTUAL published rational-model denominator
  polynomial `1+k4·u+k5·u²+k6·u³` (u = x'²+y'², i.e. the squared normalised
  sensor radius) is strictly positive for ALL u ≥ 0 — not merely on the
  bounded certified disk of Pipeline/RealCalibrationKinectImproved.lean — by
  chaining the bounded-piece and unbounded-tail lemmas of
  Pipeline/SignedCubicBoundsGlobal.lean across 8 regions that together cover
  all of `[0,∞)`, with NO gap (the boundary between the "still descending"
  and "ascending" regimes is the EXACT rational
  `Lstar := -k5/(3·k6) = 2138909339904785/4838702917098999`, not an
  approximation — both `cubic_tight_neg`'s and `cubic_bounded_piece_lower`'s
  side conditions hold there with equality, confirmed by `norm_num`).

  This closes the scope gap flagged in
  audit/IMPROVED_REAL_CALIBRATION_BOUNDS.md §6: `CVmap`'s `hden` hypothesis
  requires exactly this fact (denominator nonzero for ALL real inputs, since
  `hden` is universally quantified over `x' y' : ℝ`, not restricted to a
  disk) — see `kinect_hden_global` below, which supplies it, completing the
  `RDist`→`CVmap`/`SensorPoint` bridge via `CVmap_inverse_invOn_tight_neg`
  (reused unchanged) in `kinect_CVmap_invertible` at the end of this file.

  Reuses, unchanged: `cubic_tight_neg` (Pipeline/SignedCubicBounds.lean),
  `cubic_bounded_piece_lower`/`cubic_tail_lower`
  (Pipeline/SignedCubicBoundsGlobal.lean), `CVmap_inverse_invOn_tight_neg`
  (Pipeline/TightBoundsWithDenominator.lean), and every hypothesis already
  proved for the bounded-disk Kinect example
  (Pipeline/RealCalibrationKinectImproved.lean) — no new axioms, no
  `sorry`, no weakened conclusion.
-/

import Pipeline.SignedCubicBoundsGlobal
import Pipeline.RealCalibrationKinectImproved

/-─────────────────────────────────────────────────────────────────────────────
  The 7 split points covering [0,∞): 0, Lstar (exact), 1/2, 6/10, 7/10, 8/10,
  9/10, 1 — then the unbounded tail [1,∞).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def kinectLstar : ℝ := 2138909339904785/4838702917098999

theorem kinect_den_global_lower (u : ℝ) (hu0 : 0 ≤ u) :
    (-1 : ℝ) < ((-26617521047592133)/100000000000000000 : ℝ) * u
      + ((-427781867980957)/200000000000000 : ℝ) * u ^ 2
      + (1612900972366333/1000000000000000 : ℝ) * u ^ 3 := by
  have hc : (0:ℝ) < (1612900972366333/1000000000000000 : ℝ) := by norm_num
  have ha : ((-26617521047592133)/100000000000000000 : ℝ) ≤ 0 := by norm_num
  have hLstar_eq : ((-427781867980957)/200000000000000 : ℝ)
      + 3 * (1612900972366333/1000000000000000 : ℝ) * kinectLstar = 0 := by
    show ((-427781867980957)/200000000000000 : ℝ)
      + 3 * (1612900972366333/1000000000000000 : ℝ) * (2138909339904785/4838702917098999) = 0
    norm_num
  rcases le_total u kinectLstar with h1 | h1
  · -- Piece 0: [0, Lstar], via cubic_tight_neg
    have hb := cubic_tight_neg ((-26617521047592133)/100000000000000000)
      ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
      kinectLstar hc ha (by linarith [hLstar_eq]) u hu0 h1
    have hLval : ((-26617521047592133)/100000000000000000 : ℝ) * kinectLstar
        + ((-427781867980957)/200000000000000) * kinectLstar ^ 2
        + (1612900972366333/1000000000000000) * kinectLstar ^ 3 > -1 := by
      show ((-26617521047592133)/100000000000000000 : ℝ) * (2138909339904785/4838702917098999)
          + ((-427781867980957)/200000000000000) * (2138909339904785/4838702917098999) ^ 2
          + (1612900972366333/1000000000000000) * (2138909339904785/4838702917098999) ^ 3 > -1
      norm_num
    linarith [hb.1, hLval]
  rcases le_total u (1/2 : ℝ) with h2 | h2
  · have hvertex : ((-427781867980957)/200000000000000 : ℝ)
        + 3 * (1612900972366333/1000000000000000) * kinectLstar ≥ 0 := by linarith [hLstar_eq]
    have hfp : ((-26617521047592133)/100000000000000000 : ℝ)
        + 2 * ((-427781867980957)/200000000000000) * kinectLstar
        + 3 * (1612900972366333/1000000000000000) * kinectLstar ^ 2 ≤ 0 := by
      show ((-26617521047592133)/100000000000000000 : ℝ)
          + 2 * ((-427781867980957)/200000000000000) * (2138909339904785/4838702917098999)
          + 3 * (1612900972366333/1000000000000000) * (2138909339904785/4838702917098999) ^ 2 ≤ 0
      norm_num
    have hLU : kinectLstar ≤ (1/2:ℝ) := by
      show (2138909339904785/4838702917098999 : ℝ) ≤ 1/2; norm_num
    have hb := cubic_bounded_piece_lower ((-26617521047592133)/100000000000000000)
      ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
      kinectLstar (1/2) hc hLU hvertex hfp u h1 h2
    have hLval : ((-26617521047592133)/100000000000000000 : ℝ) * kinectLstar
        + ((-427781867980957)/200000000000000) * kinectLstar ^ 2
        + (1612900972366333/1000000000000000) * kinectLstar ^ 3
        + ((1/2:ℝ) - kinectLstar) * (((-26617521047592133)/100000000000000000 : ℝ)
            + 2 * ((-427781867980957)/200000000000000) * kinectLstar
            + 3 * (1612900972366333/1000000000000000) * kinectLstar ^ 2) > -1 := by
      show ((-26617521047592133)/100000000000000000 : ℝ) * (2138909339904785/4838702917098999)
          + ((-427781867980957)/200000000000000) * (2138909339904785/4838702917098999) ^ 2
          + (1612900972366333/1000000000000000) * (2138909339904785/4838702917098999) ^ 3
          + ((1/2:ℝ) - (2138909339904785/4838702917098999)) * (((-26617521047592133)/100000000000000000 : ℝ)
              + 2 * ((-427781867980957)/200000000000000) * (2138909339904785/4838702917098999)
              + 3 * (1612900972366333/1000000000000000) * (2138909339904785/4838702917098999) ^ 2) > -1
      norm_num
    linarith [hb, hLval]
  rcases le_total u (6/10 : ℝ) with h3 | h3
  · have hvertex : ((-427781867980957)/200000000000000 : ℝ)
        + 3 * (1612900972366333/1000000000000000) * (1/2:ℝ) ≥ 0 := by norm_num
    have hfp : ((-26617521047592133)/100000000000000000 : ℝ)
        + 2 * ((-427781867980957)/200000000000000) * (1/2:ℝ)
        + 3 * (1612900972366333/1000000000000000) * (1/2:ℝ) ^ 2 ≤ 0 := by norm_num
    have hb := cubic_bounded_piece_lower ((-26617521047592133)/100000000000000000)
      ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
      (1/2) (6/10) hc (by norm_num) hvertex hfp u h2 h3
    norm_num at hb
    linarith [hb]
  rcases le_total u (7/10 : ℝ) with h4 | h4
  · have hvertex : ((-427781867980957)/200000000000000 : ℝ)
        + 3 * (1612900972366333/1000000000000000) * (6/10:ℝ) ≥ 0 := by norm_num
    have hfp : ((-26617521047592133)/100000000000000000 : ℝ)
        + 2 * ((-427781867980957)/200000000000000) * (6/10:ℝ)
        + 3 * (1612900972366333/1000000000000000) * (6/10:ℝ) ^ 2 ≤ 0 := by norm_num
    have hb := cubic_bounded_piece_lower ((-26617521047592133)/100000000000000000)
      ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
      (6/10) (7/10) hc (by norm_num) hvertex hfp u h3 h4
    norm_num at hb
    linarith [hb]
  rcases le_total u (8/10 : ℝ) with h5 | h5
  · have hvertex : ((-427781867980957)/200000000000000 : ℝ)
        + 3 * (1612900972366333/1000000000000000) * (7/10:ℝ) ≥ 0 := by norm_num
    have hfp : ((-26617521047592133)/100000000000000000 : ℝ)
        + 2 * ((-427781867980957)/200000000000000) * (7/10:ℝ)
        + 3 * (1612900972366333/1000000000000000) * (7/10:ℝ) ^ 2 ≤ 0 := by norm_num
    have hb := cubic_bounded_piece_lower ((-26617521047592133)/100000000000000000)
      ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
      (7/10) (8/10) hc (by norm_num) hvertex hfp u h4 h5
    norm_num at hb
    linarith [hb]
  rcases le_total u (9/10 : ℝ) with h6 | h6
  · have hvertex : ((-427781867980957)/200000000000000 : ℝ)
        + 3 * (1612900972366333/1000000000000000) * (8/10:ℝ) ≥ 0 := by norm_num
    have hfp : ((-26617521047592133)/100000000000000000 : ℝ)
        + 2 * ((-427781867980957)/200000000000000) * (8/10:ℝ)
        + 3 * (1612900972366333/1000000000000000) * (8/10:ℝ) ^ 2 ≤ 0 := by norm_num
    have hb := cubic_bounded_piece_lower ((-26617521047592133)/100000000000000000)
      ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
      (8/10) (9/10) hc (by norm_num) hvertex hfp u h5 h6
    norm_num at hb
    linarith [hb]
  rcases le_total u (1 : ℝ) with h7 | h7
  · have hvertex : ((-427781867980957)/200000000000000 : ℝ)
        + 3 * (1612900972366333/1000000000000000) * (9/10:ℝ) ≥ 0 := by norm_num
    have hfp : ((-26617521047592133)/100000000000000000 : ℝ)
        + 2 * ((-427781867980957)/200000000000000) * (9/10:ℝ)
        + 3 * (1612900972366333/1000000000000000) * (9/10:ℝ) ^ 2 ≤ 0 := by norm_num
    have hb := cubic_bounded_piece_lower ((-26617521047592133)/100000000000000000)
      ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
      (9/10) 1 hc (by norm_num) hvertex hfp u h6 h7
    norm_num at hb
    linarith [hb]
  · -- Tail: [1, ∞), via cubic_tail_lower
    have hvertex : ((-427781867980957)/200000000000000 : ℝ)
        + 3 * (1612900972366333/1000000000000000) * (1:ℝ) ≥ 0 := by norm_num
    have hfp : (0:ℝ) ≤ ((-26617521047592133)/100000000000000000 : ℝ)
        + 2 * ((-427781867980957)/200000000000000) * (1:ℝ)
        + 3 * (1612900972366333/1000000000000000) * (1:ℝ) ^ 2 := by norm_num
    have hb := cubic_tail_lower ((-26617521047592133)/100000000000000000)
      ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000) 1 hc hvertex hfp u h7
    norm_num at hb
    linarith [hb]

/-- The GLOBAL `hden` hypothesis `CVmap` requires — universally quantified over
ALL real `x', y'`, not merely those in a certified disk. -/
theorem kinect_hden_global : ∀ x' y' : ℝ,
    1 + ((-26617521047592133)/100000000000000000 : ℝ) * (x' ^ 2 + y' ^ 2)
      + ((-427781867980957)/200000000000000 : ℝ) * (x' ^ 2 + y' ^ 2) ^ 2
      + (1612900972366333/1000000000000000 : ℝ) * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0 := by
  intro x' y'
  have hu0 : (0:ℝ) ≤ x' ^ 2 + y' ^ 2 := by positivity
  have := kinect_den_global_lower (x' ^ 2 + y' ^ 2) hu0
  linarith

/-─────────────────────────────────────────────────────────────────────────────
  The Kinect `RDist`→`CVmap`/`SensorPoint` bridge, completed: reuses
  `CVmap_inverse_invOn_tight_neg` (Pipeline/TightBoundsWithDenominator.lean)
  and every disk-level hypothesis already proved in
  Pipeline/RealCalibrationKinectImproved.lean, substituting the now-PROVED
  global `kinect_hden_global` for what was previously a free parameter.
─────────────────────────────────────────────────────────────────────────────-/

theorem kinect_CVmap_invertible :
    Set.InvOn
      (toComplexEquiv.symm ∘
        RDistInvTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
          (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
          ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
          (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5) (by norm_num)
          kinect_ha1 kinect_hmono1_3 kinect_hmono1_4 kinect_hc1 kinect_hge2_1
          kinect_ha4 kinect_hmono4_3 kinect_hmono4_4 kinect_hc4 kinect_hge2_4
          kinect_hsafe kinect_hcontract
        ∘ toComplexEquiv)
      (CVmap ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
        (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
        ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
        (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) kinect_hden_global)
      (toComplexEquiv.symm ''
        {z : ℂ | ‖z‖ ≤ (2/5 : ℝ) ∧ ‖RDist θ_kinect z‖
          + MPertTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
              (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
              ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
              (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5) ≤ (2/5 : ℝ)})
      (toComplexEquiv.symm '' {y : ℂ | ‖y‖
          + MPertTightNeg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
              (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
              ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
              (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) (2/5) ≤ (2/5 : ℝ)}) :=
  CVmap_inverse_invOn_tight_neg ((-946766696870327)/6250000000000000) ((-470049524307251)/200000000000000)
    (859809398651123/500000000000000) ((-26617521047592133)/100000000000000000)
    ((-427781867980957)/200000000000000) (1612900972366333/1000000000000000)
    (2856750215869397/2500000000000000000) ((-4758566792588681)/20000000000000000000) kinect_hden_global
    (2/5) (by norm_num)
    kinect_ha1 kinect_hmono1_3 kinect_hmono1_4 kinect_hc1 kinect_hge2_1
    kinect_ha4 kinect_hmono4_3 kinect_hmono4_4 kinect_hc4 kinect_hge2_4
    kinect_hsafe kinect_hcontract
