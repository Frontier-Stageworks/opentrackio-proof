/-
  Pipeline/RationalDistortionBridge.lean

  Bridges the ℂ-based RDist/existence machinery
  (RationalDistortionInjectivity.lean) back to the actual SensorPoint-based
  `CVmap`/`distortPointCV` used by `opencv_openlensio_inverse_conjugate`
  (Pipeline/InverseConjugacyApplication.lean), via the equivalence
  `SensorPoint ≃ ℂ` and `conjugate_invOn` (InverseConjugacy.lean) — the SAME
  general tool `Pipeline/ForwardConjugacy.lean`'s `screenScaleEquiv` used for
  coordinate scaling, reused here for representation transport instead.

  This is the "Connect those results to the existing corrected 2D
  OpenCV/OpenTrackIO inverse-conjugacy theorem" step: it discharges
  `opencv_openlensio_inverse_conjugate`'s `hCVInv` hypothesis on an explicit,
  checkable, positive-radius disk — not assumed, derived.
-/

import Pipeline.RationalDistortionInjectivity
import Pipeline.InverseConjugacyApplication
import InverseConjugacy

/-─────────────────────────────────────────────────────────────────────────────
  toComplexEquiv — the obvious relabeling equivalence SensorPoint ≃ ℂ.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def toComplexEquiv : SensorPoint ≃ ℂ where
  toFun ε := ⟨ε.x, ε.y⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem toComplexEquiv_re (ε : SensorPoint) : (toComplexEquiv ε).re = ε.x := rfl
theorem toComplexEquiv_im (ε : SensorPoint) : (toComplexEquiv ε).im = ε.y := rfl

/-─────────────────────────────────────────────────────────────────────────────
  RCoeffsOf — package the raw OpenCV-convention coefficients as an RCoeffs
  value, for use with RDist/RationalDistortionInjectivity.lean's machinery.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def RCoeffsOf (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ) : RCoeffs :=
  ⟨k1, k2, k3, k4, k5, k6, p1, p2⟩

/-─────────────────────────────────────────────────────────────────────────────
  CVmap_eq_RDist — the correspondence fact: CVmap, transported through
  toComplexEquiv, is exactly RDist (same formula, same point, no new
  mathematical content — only the sensorRadius/Complex.normSq bridging
  already used in Pipeline/ForwardConjugacy.lean).
─────────────────────────────────────────────────────────────────────────────-/

theorem CVmap_eq_RDist
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (hden : ∀ x' y' : ℝ, 1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
              + k6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0)
    (ε : SensorPoint) :
    toComplexEquiv (CVmap k1 k2 k3 k4 k5 k6 p1 p2 hden ε)
      = RDist (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) (toComplexEquiv ε) := by
  set θ := RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2 with hθ
  set z := toComplexEquiv ε with hz
  have hr2 : (sensorRadius ε) ^ 2 = ε.x ^ 2 + ε.y ^ 2 := Real.sq_sqrt (by positivity)
  have hnormSq : Complex.normSq z = ε.x ^ 2 + ε.y ^ 2 := by
    rw [hz]; show Complex.normSq (⟨ε.x, ε.y⟩ : ℂ) = ε.x ^ 2 + ε.y ^ 2
    simp [Complex.normSq_apply]; ring
  have hzre : z.re = ε.x := toComplexEquiv_re ε
  have hzim : z.im = ε.y := toComplexEquiv_im ε
  -- Radial ratio: Rfac θ z reduces to exactly distortXCV/distortYCV's own factor.
  have hRfac : Rfac θ z =
      (1 + k1 * (ε.x ^ 2 + ε.y ^ 2) + k2 * (ε.x ^ 2 + ε.y ^ 2) ^ 2
         + k3 * (ε.x ^ 2 + ε.y ^ 2) ^ 3) /
      (1 + k4 * (ε.x ^ 2 + ε.y ^ 2) + k5 * (ε.x ^ 2 + ε.y ^ 2) ^ 2
         + k6 * (ε.x ^ 2 + ε.y ^ 2) ^ 3) := by
    unfold Rfac Nnum Dden radial numCoeffs denCoeffs
    rw [hθ]; dsimp only [RCoeffsOf]
    rw [hnormSq]
    ring
  -- Tangential: Tang θ z reduces to distortXCV/distortYCV's own tangential term.
  have hTangRe : (Tang θ z).re = 2 * p1 * ε.x * ε.y + p2 * (ε.x ^ 2 + ε.y ^ 2 + 2 * ε.x ^ 2) := by
    show (radial (tangCoeffs θ) z * z.re + 2 * (tangCoeffs θ).p1 * z.re * z.im
        + (tangCoeffs θ).p2 * (Complex.normSq z + 2 * z.re ^ 2)) = _
    unfold tangCoeffs radial
    rw [hθ]; dsimp only [RCoeffsOf]
    rw [hnormSq, hzre, hzim]
    ring
  have hTangIm : (Tang θ z).im = p1 * (ε.x ^ 2 + ε.y ^ 2 + 2 * ε.y ^ 2) + 2 * p2 * ε.x * ε.y := by
    show (radial (tangCoeffs θ) z * z.im + (tangCoeffs θ).p1 * (Complex.normSq z + 2 * z.im ^ 2)
        + 2 * (tangCoeffs θ).p2 * z.re * z.im) = _
    unfold tangCoeffs radial
    rw [hθ]; dsimp only [RCoeffsOf]
    rw [hnormSq, hzre, hzim]
    ring
  have hRDistRe : (RDist θ z).re = Rfac θ z * z.re + (Tang θ z).re := by
    unfold RDist
    rw [Complex.add_re, Complex.real_smul, Complex.mul_re]
    simp
  have hRDistIm : (RDist θ z).im = Rfac θ z * z.im + (Tang θ z).im := by
    unfold RDist
    rw [Complex.add_im, Complex.real_smul, Complex.mul_im]
    simp
  apply Complex.ext
  · show distortXCV k1 k2 k3 k4 k5 k6 p1 p2 ε
        (denom_sensorRadius_ne_zero k4 k5 k6 hden ε) = (RDist θ z).re
    rw [hRDistRe, hRfac, hTangRe, hzre]
    simp only [distortXCV]
    rw [show (sensorRadius ε) ^ 4 = ((sensorRadius ε) ^ 2) ^ 2 from by ring,
        show (sensorRadius ε) ^ 6 = ((sensorRadius ε) ^ 2) ^ 3 from by ring, hr2]
    ring
  · show distortYCV k1 k2 k3 k4 k5 k6 p1 p2 ε
        (denom_sensorRadius_ne_zero k4 k5 k6 hden ε) = (RDist θ z).im
    rw [hRDistIm, hRfac, hTangIm, hzim]
    simp only [distortYCV]
    rw [show (sensorRadius ε) ^ 4 = ((sensorRadius ε) ^ 2) ^ 2 from by ring,
        show (sensorRadius ε) ^ 6 = ((sensorRadius ε) ^ 2) ^ 3 from by ring, hr2]
    ring

/-─────────────────────────────────────────────────────────────────────────────
  RDist_inverse_invOn — packages RDist_exists_unique_preimage's ∃! into an
  actual Set.InvOn fact in ℂ, by extracting the unique preimage via classical
  choice on the buffer disk. Outside the buffer disk (‖y‖+MPert>R), the
  constructed function is unspecified junk (0) — never used, since B below
  is exactly the buffer disk, matching `Function.invFun`-style discipline:
  the junk value's existence is visible and documented, not silently relied
  upon outside where it is actually characterized.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def RDistInv (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (hcontract : LPert θ R < 1) (y : ℂ) : ℂ :=
  open Classical in
  if h : ‖y‖ + MPert θ R ≤ R then
    (RDist_exists_unique_preimage θ R hR hsafe hcontract y h).exists.choose
  else 0

/-
  NOTE on the domain A below. A naive `{z | ‖z‖ ≤ R}` is too large for
  LeftInvOn: a point z in the full disk need not have RDist θ z land back in
  the buffer region B where `RDistInv` is characterized by
  `RDist_exists_unique_preimage` (outside B, `RDistInv` is unspecified junk,
  by construction, exactly as `Function.invFun`'s junk-value discipline
  requires making explicit). The correct domain is the subset of the disk
  whose IMAGE under RDist also lands in the buffer — expressed directly
  rather than assumed.
-/

theorem RDist_inverse_invOn (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (hcontract : LPert θ R < 1) :
    Set.InvOn (RDistInv θ R hR hsafe hcontract) (RDist θ)
      {z : ℂ | ‖z‖ ≤ R ∧ ‖RDist θ z‖ + MPert θ R ≤ R} {y : ℂ | ‖y‖ + MPert θ R ≤ R} := by
  constructor
  · -- LeftInvOn: ∀ z with ‖z‖≤R and RDist θ z in the buffer, RDistInv (RDist θ z) = z
    intro z hz
    obtain ⟨hzR, hyR⟩ := hz
    have huniq := RDist_exists_unique_preimage θ R hR hsafe hcontract (RDist θ z) hyR
    have hchoose_spec := huniq.exists.choose_spec
    have hval : RDistInv θ R hR hsafe hcontract (RDist θ z) = huniq.exists.choose := by
      show (if h : ‖RDist θ z‖ + MPert θ R ≤ R then
              (RDist_exists_unique_preimage θ R hR hsafe hcontract (RDist θ z) h).exists.choose
            else 0) = huniq.exists.choose
      rw [dif_pos hyR]
    rw [hval]
    exact huniq.unique hchoose_spec ⟨hzR, rfl⟩
  · -- RightInvOn: ∀ y ∈ buffer, RDist θ (RDistInv y) = y
    intro y hy
    have hy' : ‖y‖ + MPert θ R ≤ R := hy
    have hval : RDistInv θ R hR hsafe hcontract y
        = (RDist_exists_unique_preimage θ R hR hsafe hcontract y hy').exists.choose := by
      show (if h : ‖y‖ + MPert θ R ≤ R then
              (RDist_exists_unique_preimage θ R hR hsafe hcontract y h).exists.choose
            else 0) = (RDist_exists_unique_preimage θ R hR hsafe hcontract y hy').exists.choose
      rw [dif_pos hy']
    rw [hval]
    exact (RDist_exists_unique_preimage θ R hR hsafe hcontract y hy').exists.choose_spec.2

/-─────────────────────────────────────────────────────────────────────────────
  CVmap_inverse_invOn — the final connection: transports RDist_inverse_invOn
  through toComplexEquiv (via conjugate_invOn — a representation-transport
  use, not a coordinate-scaling use) and CVmap_eq_RDist, to give an EXPLICIT,
  DERIVED (not assumed) witness for `opencv_openlensio_inverse_conjugate`'s
  `hCVInv` hypothesis, on genuine, checkable, positive-radius sets.
─────────────────────────────────────────────────────────────────────────────-/

theorem CVmap_inverse_invOn
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (hden : ∀ x' y' : ℝ, 1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
              + k6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0)
    (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) R < 1)
    (hcontract : LPert (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) R < 1) :
    Set.InvOn
      (toComplexEquiv.symm ∘
        RDistInv (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) R hR hsafe hcontract ∘ toComplexEquiv)
      (CVmap k1 k2 k3 k4 k5 k6 p1 p2 hden)
      (toComplexEquiv.symm ''
        {z : ℂ | ‖z‖ ≤ R ∧ ‖RDist (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z‖
                    + MPert (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) R ≤ R})
      (toComplexEquiv.symm '' {y : ℂ | ‖y‖ + MPert (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) R ≤ R}) := by
  set θ := RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2 with hθ
  have hconj : ∀ x : ℂ,
      CVmap k1 k2 k3 k4 k5 k6 p1 p2 hden (toComplexEquiv.symm x) = toComplexEquiv.symm (RDist θ x) := by
    intro x
    have h := CVmap_eq_RDist k1 k2 k3 k4 k5 k6 p1 p2 hden (toComplexEquiv.symm x)
    rw [toComplexEquiv.apply_symm_apply] at h
    have h2 := congrArg toComplexEquiv.symm h
    rwa [Equiv.symm_apply_apply] at h2
  have hmain := conjugate_invOn toComplexEquiv.symm (RDist θ)
    (RDistInv θ R hR hsafe hcontract) (CVmap k1 k2 k3 k4 k5 k6 p1 p2 hden)
    {z : ℂ | ‖z‖ ≤ R ∧ ‖RDist θ z‖ + MPert θ R ≤ R} {y : ℂ | ‖y‖ + MPert θ R ≤ R}
    hconj (RDist_inverse_invOn θ R hR hsafe hcontract)
  simpa [Equiv.symm_symm] using hmain
