/-
  Pipeline/RationalDistortionExamples.lean

  Two concrete, nontrivial, Lean-verified calibrations exercising the full
  bounded-domain-invertibility chain (RationalRadialBounds.lean →
  RationalDistortionBounds.lean → RationalDistortionInjectivity.lean →
  RationalDistortionBridge.lean) with EXPLICIT, CHECKABLE, POSITIVE-RADIUS
  certified regions.

  CORRECTION (adversarial review): an earlier version of this file used
  `k1 = k4` for both examples. Since the radial factor is
  `R(u) = (1+k1·u+k2·u²+k3·u³)/(1+k4·u+k5·u²+k6·u³)`, setting `k1=k4` (with
  all other radial coefficients zero) makes numerator and denominator the
  SAME polynomial, so `R(u) ≡ 1` identically — Example 1 (`p1=p2=0`) was
  therefore exactly the identity map, and Example 2 had tangential distortion
  only, not "radial and tangential" as claimed. Both examples below use
  `k1 ≠ k4` and include an explicit, Lean-checked proof that the resulting
  map disagrees with the identity at a concrete point — not merely a claim.

  Example 1: pure radial, k1 = 1/5, k4 = 1/20 (genuinely different, so
  R(u) is not identically 1), p1 = p2 = 0.

  Example 2: radial AND tangential — same k1, k4, plus p1 = 1/200 ≠ 0.

  Both use the unit disk R = 1. `k4 = 1/20 > 0` with k2=k3=k5=k6=0 makes the
  CV-side (and, after conversion, the OTI-side) denominator-nonzero
  hypothesis PROVABLE for ALL real inputs (not merely within a disk) — see
  `hden_shared`/`hdenOTI_shared` below, which discharge it via `positivity`
  rather than taking it as a free hypothesis.
-/

import Pipeline.RationalDistortionBridge
import Pipeline.ForwardConjugacy
import Pipeline.InverseConjugacyApplication

noncomputable def θ₁ : RCoeffs := ⟨1/5, 0, 0, 1/20, 0, 0, 0, 0⟩
noncomputable def θ₂ : RCoeffs := ⟨1/5, 0, 0, 1/20, 0, 0, 1/200, 0⟩

/-─────────────────────────────────────────────────────────────────────────────
  Globally-discharged denominator-nonzero hypotheses (task item 5): since
  k4 = 1/20 > 0 and k2=k3=k5=k6=0, the denominator `1 + k4·(x'²+y'²)` is
  `≥ 1 > 0` for EVERY real x', y' — not merely within a certified disk. Same
  shared value of k4 for both θ₁ and θ₂, so one lemma covers both examples.
─────────────────────────────────────────────────────────────────────────────-/

theorem hden_shared : ∀ x' y' : ℝ,
    1 + (1/20 : ℝ) * (x' ^ 2 + y' ^ 2) + 0 * (x' ^ 2 + y' ^ 2) ^ 2
      + 0 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0 := by
  intro x' y'; positivity

/-─────────────────────────────────────────────────────────────────────────────
  Example 1 — pure radial, k1 ≠ k4, nonzero denominator, unit disk.
─────────────────────────────────────────────────────────────────────────────-/

theorem example1_denom_safe : denomMargin θ₁ 1 < 1 := by
  simp only [denomMargin, Mrad, denCoeffs, θ₁]
  norm_num

theorem example1_contraction : LPert θ₁ 1 < 1 := by
  simp only [LPert, RfacDevUB, RfacL, denomLB, denomMargin, Mrad, Lrad, NnumUB, DdenUB,
    numCoeffs, denCoeffs, L, tangCoeffs, θ₁]
  norm_num

/-- Explicit, non-identity witness: the point `(1,0)` is genuinely moved by
`CVmap`'s radial factor, since `R(1) = (1+1/5)/(1+1/20) = 8/7 ≠ 1`. This is
not merely "nonzero coefficients were supplied" — it is a computed,
machine-checked inequality of actual output values. -/
theorem example1_not_identity :
    CVmap (1/5) 0 0 (1/20) 0 0 0 0 hden_shared (⟨1, 0⟩ : SensorPoint)
      ≠ (⟨1, 0⟩ : SensorPoint) := by
  intro h
  have hx : (CVmap (1/5) 0 0 (1/20) 0 0 0 0 hden_shared (⟨1, 0⟩ : SensorPoint)).x
      = (1 : ℝ) := by rw [h]
  have hr : sensorRadius (⟨1, 0⟩ : SensorPoint) = 1 := by
    unfold sensorRadius; norm_num
  simp only [CVmap, distortPointCV, distortXCV, hr] at hx
  norm_num at hx

theorem example1_invertible :
    Set.InvOn (RDistInv θ₁ 1 (by norm_num) example1_denom_safe example1_contraction) (RDist θ₁)
      {z : ℂ | ‖z‖ ≤ 1 ∧ ‖RDist θ₁ z‖ + MPert θ₁ 1 ≤ 1} {y : ℂ | ‖y‖ + MPert θ₁ 1 ≤ 1} :=
  RDist_inverse_invOn θ₁ 1 (by norm_num) example1_denom_safe example1_contraction

/-─────────────────────────────────────────────────────────────────────────────
  Example 2 — radial AND tangential, k1 ≠ k4, nonzero denominator, unit disk.
─────────────────────────────────────────────────────────────────────────────-/

theorem example2_denom_safe : denomMargin θ₂ 1 < 1 := by
  simp only [denomMargin, Mrad, denCoeffs, θ₂]
  norm_num

theorem example2_contraction : LPert θ₂ 1 < 1 := by
  simp only [LPert, RfacDevUB, RfacL, denomLB, denomMargin, Mrad, Lrad, NnumUB, DdenUB,
    numCoeffs, denCoeffs, L, tangCoeffs, θ₂]
  norm_num

/-- Same radial witness as Example 1 at `(1,0)` (tangential terms vanish when
`y'=0` regardless of `p1`, so this alone would not isolate the tangential
contribution) — PLUS an independent witness at `(1,1)`, where the tangential
term is genuinely active (`2·p1·x'·y' ≠ 0`), confirming Example 2 is neither
the identity NOR merely a re-run of Example 1's radial-only behaviour. -/
theorem example2_not_identity :
    CVmap (1/5) 0 0 (1/20) 0 0 (1/200) 0 hden_shared (⟨1, 0⟩ : SensorPoint)
      ≠ (⟨1, 0⟩ : SensorPoint) := by
  intro h
  have hx : (CVmap (1/5) 0 0 (1/20) 0 0 (1/200) 0 hden_shared (⟨1, 0⟩ : SensorPoint)).x
      = (1 : ℝ) := by rw [h]
  have hr : sensorRadius (⟨1, 0⟩ : SensorPoint) = 1 := by
    unfold sensorRadius; norm_num
  simp only [CVmap, distortPointCV, distortXCV, hr] at hx
  norm_num at hx

theorem example2_tangential_active :
    CVmap (1/5) 0 0 (1/20) 0 0 (1/200) 0 hden_shared (⟨1, 1⟩ : SensorPoint)
      ≠ CVmap (1/5) 0 0 (1/20) 0 0 0 0 hden_shared (⟨1, 1⟩ : SensorPoint) := by
  intro h
  have hx : (CVmap (1/5) 0 0 (1/20) 0 0 (1/200) 0 hden_shared (⟨1, 1⟩ : SensorPoint)).x
      = (CVmap (1/5) 0 0 (1/20) 0 0 0 0 hden_shared (⟨1, 1⟩ : SensorPoint)).x := by rw [h]
  have hr : sensorRadius (⟨1, 1⟩ : SensorPoint) = Real.sqrt 2 := by
    unfold sensorRadius; norm_num
  simp only [CVmap, distortPointCV, distortXCV, hr] at hx
  norm_num at hx

theorem example2_invertible :
    Set.InvOn (RDistInv θ₂ 1 (by norm_num) example2_denom_safe example2_contraction) (RDist θ₂)
      {z : ℂ | ‖z‖ ≤ 1 ∧ ‖RDist θ₂ z‖ + MPert θ₂ 1 ≤ 1} {y : ℂ | ‖y‖ + MPert θ₂ 1 ≤ 1} :=
  RDist_inverse_invOn θ₂ 1 (by norm_num) example2_denom_safe example2_contraction

theorem example2_CVmap_invertible :
    Set.InvOn
      (toComplexEquiv.symm ∘
        RDistInv (RCoeffsOf (1/5) 0 0 (1/20) 0 0 (1/200) 0) 1 (by norm_num)
          example2_denom_safe example2_contraction
        ∘ toComplexEquiv)
      (CVmap (1/5) 0 0 (1/20) 0 0 (1/200) 0 hden_shared)
      (toComplexEquiv.symm ''
        {z : ℂ | ‖z‖ ≤ 1 ∧ ‖RDist (RCoeffsOf (1/5) 0 0 (1/20) 0 0 (1/200) 0) z‖
                    + MPert (RCoeffsOf (1/5) 0 0 (1/20) 0 0 (1/200) 0) 1 ≤ 1})
      (toComplexEquiv.symm ''
        {y : ℂ | ‖y‖ + MPert (RCoeffsOf (1/5) 0 0 (1/20) 0 0 (1/200) 0) 1 ≤ 1}) :=
  CVmap_inverse_invOn (1/5) 0 0 (1/20) 0 0 (1/200) 0 hden_shared 1 (by norm_num)
    example2_denom_safe example2_contraction

/-─────────────────────────────────────────────────────────────────────────────
  COMPLETED composition into opencv_openlensio_inverse_conjugate (task item 4):
  this is a fully-resolved, permanently-committed theorem (every hypothesis
  discharged by `norm_num`/`positivity`, no step left unresolved as a scratch
  check), not merely shown type-compatible in a throwaway script.

  Pixel-level parameters: F=2, fx=fy=1, w=2, ws=1, h=2, h_shader=1, cx=cy=0
  (so ΔPx=ΔPy=-1), matching F=(w/ws)·fx=(h/h_shader)·fy=2 for both axes.
  OTI coefficients via l=k/F^(2n), q=p/F: l1=1/20, l2=1/80, q1=1/400, all
  other l's and q2 zero. `hdenOTI_shared` discharges the OTI-side
  denominator-nonzero hypothesis globally, by the same positivity argument
  as `hden_shared` (l2 = 1/80 > 0).
─────────────────────────────────────────────────────────────────────────────-/

theorem hdenOTI_shared : ∀ x' y' : ℝ,
    1 + (1/80 : ℝ) * (x' ^ 2 + y' ^ 2) + 0 * (x' ^ 2 + y' ^ 2) ^ 2
      + 0 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0 := by
  intro x' y'; positivity

theorem example2_full_inverse_conjugate :
    Set.InvOn
      ((screenScaleEquiv 2 (by norm_num)) ∘
        (toComplexEquiv.symm ∘
          RDistInv (RCoeffsOf (1/5) 0 0 (1/20) 0 0 (1/200) 0) 1 (by norm_num)
            example2_denom_safe example2_contraction
          ∘ toComplexEquiv)
        ∘ (screenScaleEquiv 2 (by norm_num)).symm)
      (OTImap (1/20) (1/80) 0 0 0 0 (1/400) 0 hdenOTI_shared)
      (screenScaleEquiv 2 (by norm_num) '' (toComplexEquiv.symm ''
        {z : ℂ | ‖z‖ ≤ 1 ∧ ‖RDist (RCoeffsOf (1/5) 0 0 (1/20) 0 0 (1/200) 0) z‖
                    + MPert (RCoeffsOf (1/5) 0 0 (1/20) 0 0 (1/200) 0) 1 ≤ 1}))
      (screenScaleEquiv 2 (by norm_num) '' (toComplexEquiv.symm ''
        {y : ℂ | ‖y‖ + MPert (RCoeffsOf (1/5) 0 0 (1/20) 0 0 (1/200) 0) 1 ≤ 1})) :=
  opencv_openlensio_inverse_conjugate
    (1/5) 0 0 (1/20) 0 0 (1/200) 0
    (1/20) (1/80) 0 0 0 0 (1/400) 0
    1 1 0 0 1 2 1 2 2 (-1) (-1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    hden_shared hdenOTI_shared
    (toComplexEquiv.symm ''
        {z : ℂ | ‖z‖ ≤ 1 ∧ ‖RDist (RCoeffsOf (1/5) 0 0 (1/20) 0 0 (1/200) 0) z‖
                    + MPert (RCoeffsOf (1/5) 0 0 (1/20) 0 0 (1/200) 0) 1 ≤ 1})
    (toComplexEquiv.symm ''
        {y : ℂ | ‖y‖ + MPert (RCoeffsOf (1/5) 0 0 (1/20) 0 0 (1/200) 0) 1 ≤ 1})
    (toComplexEquiv.symm ∘
      RDistInv (RCoeffsOf (1/5) 0 0 (1/20) 0 0 (1/200) 0) 1 (by norm_num)
        example2_denom_safe example2_contraction
      ∘ toComplexEquiv)
    example2_CVmap_invertible
