/-
  Pipeline/RationalDistortionExamples.lean

  Two concrete, nontrivial, Lean-verified calibrations exercising the full
  bounded-domain-invertibility chain (RationalRadialBounds.lean →
  RationalDistortionBounds.lean → RationalDistortionInjectivity.lean →
  RationalDistortionBridge.lean) with EXPLICIT, CHECKABLE, POSITIVE-RADIUS
  certified regions — not merely a trivial/identity instantiation.

  Example 1: pure radial, with a genuinely nonzero denominator coefficient
  (k1 = k4 = 1/10, all other radial coefficients and both tangential
  coefficients zero) — exercises denominator safety and the rational-factor
  contraction bound without any tangential contribution.

  Example 2: radial AND tangential (k1 = k4 = 1/10, p1 = 1/100) — exercises
  the full combined bound/Lipschitz machinery, including the tangential
  Lipschitz contribution to the contraction constant.

  Both use the unit disk R = 1. All side conditions (`denomMargin θ R < 1`,
  `LPert θ R < 1`) are verified by `norm_num`, not asserted.
-/

import Pipeline.RationalDistortionBridge

noncomputable def θ₁ : RCoeffs := ⟨1/10, 0, 0, 1/10, 0, 0, 0, 0⟩
noncomputable def θ₂ : RCoeffs := ⟨1/10, 0, 0, 1/10, 0, 0, 1/100, 0⟩

/-─────────────────────────────────────────────────────────────────────────────
  Example 1 — pure radial, nonzero denominator, unit disk.
─────────────────────────────────────────────────────────────────────────────-/

theorem example1_denom_safe : denomMargin θ₁ 1 < 1 := by
  simp only [denomMargin, Mrad, denCoeffs, θ₁]
  norm_num

theorem example1_contraction : LPert θ₁ 1 < 1 := by
  simp only [LPert, RfacDevUB, RfacL, denomLB, denomMargin, Mrad, Lrad, NnumUB, DdenUB,
    numCoeffs, denCoeffs, L, tangCoeffs, θ₁]
  norm_num

theorem example1_invertible :
    Set.InvOn (RDistInv θ₁ 1 (by norm_num) example1_denom_safe example1_contraction) (RDist θ₁)
      {z : ℂ | ‖z‖ ≤ 1 ∧ ‖RDist θ₁ z‖ + MPert θ₁ 1 ≤ 1} {y : ℂ | ‖y‖ + MPert θ₁ 1 ≤ 1} :=
  RDist_inverse_invOn θ₁ 1 (by norm_num) example1_denom_safe example1_contraction

/-─────────────────────────────────────────────────────────────────────────────
  Example 2 — radial AND tangential, nonzero denominator, unit disk.
─────────────────────────────────────────────────────────────────────────────-/

theorem example2_denom_safe : denomMargin θ₂ 1 < 1 := by
  simp only [denomMargin, Mrad, denCoeffs, θ₂]
  norm_num

theorem example2_contraction : LPert θ₂ 1 < 1 := by
  simp only [LPert, RfacDevUB, RfacL, denomLB, denomMargin, Mrad, Lrad, NnumUB, DdenUB,
    numCoeffs, denCoeffs, L, tangCoeffs, θ₂]
  norm_num

theorem example2_invertible :
    Set.InvOn (RDistInv θ₂ 1 (by norm_num) example2_denom_safe example2_contraction) (RDist θ₂)
      {z : ℂ | ‖z‖ ≤ 1 ∧ ‖RDist θ₂ z‖ + MPert θ₂ 1 ≤ 1} {y : ℂ | ‖y‖ + MPert θ₂ 1 ≤ 1} :=
  RDist_inverse_invOn θ₂ 1 (by norm_num) example2_denom_safe example2_contraction

/-─────────────────────────────────────────────────────────────────────────────
  Example 2, continued — feeding directly into CVmap_inverse_invOn, i.e. the
  SensorPoint/CVmap-level derived inverse (the form `hCVInv` in
  `opencv_openlensio_inverse_conjugate` actually needs), confirming the full
  chain composes end to end for this concrete, nontrivial, radial+tangential
  calibration.
─────────────────────────────────────────────────────────────────────────────-/

theorem example2_CVmap_invertible
    (hden : ∀ x' y' : ℝ, 1 + (1/10 : ℝ) * (x' ^ 2 + y' ^ 2) + 0 * (x' ^ 2 + y' ^ 2) ^ 2
              + 0 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0) :
    Set.InvOn
      (toComplexEquiv.symm ∘
        RDistInv (RCoeffsOf (1/10) 0 0 (1/10) 0 0 (1/100) 0) 1 (by norm_num)
          example2_denom_safe example2_contraction
        ∘ toComplexEquiv)
      (CVmap (1/10) 0 0 (1/10) 0 0 (1/100) 0 hden)
      (toComplexEquiv.symm ''
        {z : ℂ | ‖z‖ ≤ 1 ∧ ‖RDist (RCoeffsOf (1/10) 0 0 (1/10) 0 0 (1/100) 0) z‖
                    + MPert (RCoeffsOf (1/10) 0 0 (1/10) 0 0 (1/100) 0) 1 ≤ 1})
      (toComplexEquiv.symm ''
        {y : ℂ | ‖y‖ + MPert (RCoeffsOf (1/10) 0 0 (1/10) 0 0 (1/100) 0) 1 ≤ 1}) :=
  CVmap_inverse_invOn (1/10) 0 0 (1/10) 0 0 (1/100) 0 hden 1 (by norm_num)
    example2_denom_safe example2_contraction
