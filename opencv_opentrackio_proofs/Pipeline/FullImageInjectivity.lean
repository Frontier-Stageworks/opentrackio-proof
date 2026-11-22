/-
  Pipeline/FullImageInjectivity.lean

  Formalizes "the certified disk contains the whole image rectangle" as an
  actual Lean theorem, using TUM fr2's real camera intrinsics (fx, fy, cx, cy)
  and real image dimensions (640×480) — replacing the numerical corner-radius
  calculation of audit/IMPROVED_REAL_CALIBRATION_BOUNDS.md §5a with a
  kernel-checked proof, and connecting it to a genuine INJECTIVITY theorem
  for `CVmap` over the full pixel rectangle.

  Pixel-to-normalised-coordinate convention (the standard pinhole relation,
  the same one used throughout this repository's `F`/`ΔPx`/`ΔPy` pixel-level
  theorems, e.g. Pipeline/PixelIffCorrected.lean): a pixel coordinate
  `(px, py)` corresponds to the normalised sensor point
  `⟨(px - cx)/fx, (py - cy)/fy⟩`.

  SCOPE, STATED EXPLICITLY (task item 3's required distinction): this file
  proves FULL-IMAGE INJECTIVITY — that `CVmap` does not send two distinct
  pixels in the ENTIRE image rectangle to the same distorted point. It does
  NOT claim that every pixel's inverse EXISTS and lands back in the same
  certified region — that stronger EXISTENCE claim (`CVmap_inverse_invOn_tight`
  via `fr2_CVmap_invertible_capstone`, Pipeline/RealCalibrationExamplesImproved.lean)
  is restricted to the smaller MPert-buffered sub-region, exactly as
  documented in audit/IMPROVED_REAL_CALIBRATION_BOUNDS.md §5a. Conflating
  "injective on the full disk" with "invertible-with-image-in-the-same-set
  on the full disk" would be the overclaim this file is designed to avoid —
  see `fr2_full_image_injective` vs `fr2_CVmap_invertible_capstone` below.

  Reuses, unchanged: `CVmap_injective_on_disk_tight_pos`
  (Pipeline/TightBoundsInjectivity.lean) and every hypothesis already proved
  for the fr2 capstone example (Pipeline/RealCalibrationExamplesImproved.lean).

  Does not modify any existing file, weaken any existing theorem, or
  introduce axioms.
-/

import Pipeline.TightBoundsInjectivity
import Pipeline.RealCalibrationExamplesImproved

/-─────────────────────────────────────────────────────────────────────────────
  A value lying in a real interval [A,B] has its square bounded by the larger
  of the two endpoint squares — pure algebra (case split on sign), no
  calculus.
─────────────────────────────────────────────────────────────────────────────-/

theorem sq_le_max_of_mem_Icc (A B y : ℝ) (hA : A ≤ y) (hB : y ≤ B) :
    y ^ 2 ≤ max (A ^ 2) (B ^ 2) := by
  rcases lt_or_ge y 0 with hy | hy
  · have h2 : A ≤ 0 := le_trans hA hy.le
    calc y ^ 2 ≤ A ^ 2 := by nlinarith
      _ ≤ max (A ^ 2) (B ^ 2) := le_max_left _ _
  · have h2 : (0:ℝ) ≤ B := le_trans hy hB
    calc y ^ 2 ≤ B ^ 2 := by nlinarith
      _ ≤ max (A ^ 2) (B ^ 2) := le_max_right _ _

/-─────────────────────────────────────────────────────────────────────────────
  TUM fr2's actual intrinsics (fx=520.908620, fy=521.007327, cx=325.141442,
  cy=249.701764 — ORB-SLAM2 TUM2.yaml, audit/REAL_CALIBRATION_VALIDATION.md
  §1a) and actual image dimensions (640×480, Sturm et al. 2012 §IV): every
  pixel in the FULL image rectangle maps to a normalised sensor point within
  the certified radius-79/100 disk.
─────────────────────────────────────────────────────────────────────────────-/

theorem fr2_image_rect_subset_cert_disk (px py : ℝ)
    (hpx0 : 0 ≤ px) (hpxw : px ≤ 640) (hpy0 : 0 ≤ py) (hpyh : py ≤ 480) :
    ((px - 325141442/1000000) / (520908620/1000000)) ^ 2
      + ((py - 249701764/1000000) / (521007327/1000000)) ^ 2 ≤ ((79:ℝ)/100) ^ 2 := by
  have hx : ((0:ℝ) - 325141442/1000000) ≤ px - 325141442/1000000 := by linarith
  have hx2 : px - 325141442/1000000 ≤ (640:ℝ) - 325141442/1000000 := by linarith
  have hy : ((0:ℝ) - 249701764/1000000) ≤ py - 249701764/1000000 := by linarith
  have hy2 : py - 249701764/1000000 ≤ (480:ℝ) - 249701764/1000000 := by linarith
  have hxsq := sq_le_max_of_mem_Icc ((0:ℝ) - 325141442/1000000) ((640:ℝ) - 325141442/1000000)
    (px - 325141442/1000000) hx hx2
  have hysq := sq_le_max_of_mem_Icc ((0:ℝ) - 249701764/1000000) ((480:ℝ) - 249701764/1000000)
    (py - 249701764/1000000) hy hy2
  have hxmax : max (((0:ℝ) - 325141442/1000000) ^ 2) (((640:ℝ) - 325141442/1000000) ^ 2)
      = ((0:ℝ) - 325141442/1000000) ^ 2 := by
    rw [max_eq_left]; nlinarith
  have hymax : max (((0:ℝ) - 249701764/1000000) ^ 2) (((480:ℝ) - 249701764/1000000) ^ 2)
      = ((0:ℝ) - 249701764/1000000) ^ 2 := by
    rw [max_eq_left]; nlinarith
  rw [hxmax] at hxsq
  rw [hymax] at hysq
  rw [div_pow, div_pow]
  have hfx2 : ((520908620/1000000 : ℝ)) ^ 2 > 0 := by norm_num
  have hfy2 : ((521007327/1000000 : ℝ)) ^ 2 > 0 := by norm_num
  have h1 : (px - 325141442/1000000) ^ 2 / (520908620/1000000:ℝ) ^ 2
      ≤ ((0:ℝ) - 325141442/1000000) ^ 2 / (520908620/1000000:ℝ) ^ 2 :=
    div_le_div_of_nonneg_right hxsq hfx2.le
  have h2 : (py - 249701764/1000000) ^ 2 / (521007327/1000000:ℝ) ^ 2
      ≤ ((0:ℝ) - 249701764/1000000) ^ 2 / (521007327/1000000:ℝ) ^ 2 :=
    div_le_div_of_nonneg_right hysq hfy2.le
  have hfinal : ((0:ℝ) - 325141442/1000000) ^ 2 / (520908620/1000000:ℝ) ^ 2
      + ((0:ℝ) - 249701764/1000000) ^ 2 / (521007327/1000000:ℝ) ^ 2 ≤ ((79:ℝ)/100) ^ 2 := by
    norm_num
  linarith [h1, h2, hfinal]

/-─────────────────────────────────────────────────────────────────────────────
  FULL-IMAGE INJECTIVITY: `CVmap` (fr2's real coefficients) does not identify
  any two distinct pixels within the ENTIRE 640×480 image rectangle.
─────────────────────────────────────────────────────────────────────────────-/

theorem fr2_full_image_injective :
    Set.InjOn
      (CVmap (231222/1000000) (-784899/1000000) (917205/1000000) 0 0 0
        (-3257/1000000) (-105/1000000) hden_fr2_improved)
      (toComplexEquiv.symm ''
        ((fun (p : ℝ × ℝ) => (⟨(p.1 - 325141442/1000000) / (520908620/1000000),
            (p.2 - 249701764/1000000) / (521007327/1000000)⟩ : ℂ))
          '' {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 640 ∧ 0 ≤ p.2 ∧ p.2 ≤ 480})) := by
  apply Set.InjOn.mono _
    (CVmap_injective_on_disk_tight_pos (231222/1000000) (-784899/1000000) (917205/1000000)
      (-3257/1000000) (-105/1000000) hden_fr2_improved (79/100) (by norm_num)
      fr2_disc_h_capstone fr2_disc_g_capstone fr2_disc_psi_capstone fr2_k3_pos fr2_contraction_capstone)
  rintro _ ⟨_, ⟨⟨px, py⟩, ⟨hpx0, hpxw, hpy0, hpyh⟩, rfl⟩, rfl⟩
  refine ⟨_, ?_, rfl⟩
  show ‖(⟨(px - 325141442/1000000) / (520908620/1000000),
      (py - 249701764/1000000) / (521007327/1000000)⟩ : ℂ)‖ ≤ (79/100 : ℝ)
  have hsq := fr2_image_rect_subset_cert_disk px py hpx0 hpxw hpy0 hpyh
  rw [Complex.norm_def, Complex.normSq_mk]
  have hle : (((px - 325141442/1000000) / (520908620/1000000)) ^ 2
      + ((py - 249701764/1000000) / (521007327/1000000)) ^ 2) ≤ ((79:ℝ)/100) ^ 2 := hsq
  have h2 : Real.sqrt (((px - 325141442/1000000) / (520908620/1000000)) * ((px - 325141442/1000000) / (520908620/1000000))
      + (py - 249701764/1000000) / (521007327/1000000) * ((py - 249701764/1000000) / (521007327/1000000)))
      ≤ Real.sqrt (((79:ℝ)/100) ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith [hle]
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 79/100)] at h2
