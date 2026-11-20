/-
  Pipeline/TightBoundsNoDenominator.lean

  Specializes the signed-cubic tightening (Pipeline/SignedCubicBounds.lean) to
  the TRIVIAL-DENOMINATOR case (k4=k5=k6=0, i.e. Dden θ z ≡ 1, Rfac θ z =
  1 + radial(numCoeffs θ) z exactly) — the case that covers the TUM fr1/fr2
  real calibrations (audit/REAL_CALIBRATION_VALIDATION.md), where no
  quotient-rule machinery is needed at all since there is no denominator to
  take a Lipschitz/boundedness estimate of.

  Produces a full, independent, parallel Banach-fixed-point existence/
  uniqueness chain (mirroring RationalDistortionInjectivity.lean's structure
  exactly, substituting MPertTightPos/LPertTightPos for MPert/LPert), then
  bridges to CVmap by REUSING (not reproving) CVmap_eq_RDist and
  toComplexEquiv from RationalDistortionBridge.lean.

  Reuses, unchanged: `M`/`L`/`phi_bounded`/`phi_lipschitz` for the tangential
  part (InverseApproximation.lean, via `tangCoeffs`), `normSq_lipschitz`,
  `cubic_tight_pos`/`k_bound_pos` (SignedCubicBounds.lean),
  `CVmap_eq_RDist`/`toComplexEquiv` (RationalDistortionBridge.lean),
  `conjugate_invOn` (InverseConjugacy.lean).

  Does not modify any existing file, weaken any existing theorem, or
  introduce axioms.
-/

import Pipeline.SignedCubicBounds
import Pipeline.RationalDistortionBridge

/-─────────────────────────────────────────────────────────────────────────────
  Tight constants for the trivial-denominator, discriminant-positive case.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def RfacDevUBTightPos (k1 k2 k3 R : ℝ) : ℝ :=
  |k1 * R ^ 2 + k2 * R ^ 4 + k3 * R ^ 6|

noncomputable def RfacLTightPos (k1 k2 k3 R : ℝ) : ℝ :=
  2 * R * max k1 (k1 + 2 * k2 * R ^ 2 + 4 * k3 * R ^ 4)

noncomputable def MPertTightPos (k1 k2 k3 p1 p2 R : ℝ) : ℝ :=
  RfacDevUBTightPos k1 k2 k3 R * R + M (⟨0, 0, 0, p1, p2⟩ : Coeffs) R

noncomputable def LPertTightPos (k1 k2 k3 p1 p2 R : ℝ) : ℝ :=
  RfacDevUBTightPos k1 k2 k3 R + RfacLTightPos k1 k2 k3 R * R + L (⟨0, 0, 0, p1, p2⟩ : Coeffs) R

/-─────────────────────────────────────────────────────────────────────────────
  Bridging the cubic/quadratic real-number facts to `radial`/ℂ. Hypotheses
  `hdisc_h`/`hdisc_g`/`hdisc_psi` are exactly `cubic_tight_pos`/`k_bound_pos`'s
  own discriminant conditions, stated with U := R^2.
─────────────────────────────────────────────────────────────────────────────-/

theorem radial_tight_bound_pos (k1 k2 k3 R : ℝ) (hR : 0 ≤ R)
    (hdisc_h : k2 ^ 2 ≤ 4 * k1 * k3)
    (hdisc_g : (k2 + k3 * R ^ 2) ^ 2 ≤ 4 * (k1 + k2 * R ^ 2 + k3 * R ^ 4) * k3)
    (hc : 0 < k3) (z : ℂ) (hz : ‖z‖ ≤ R) :
    |radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z| ≤ RfacDevUBTightPos k1 k2 k3 R := by
  have hu0 : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
  have huU : Complex.normSq z ≤ R ^ 2 := by
    rw [← Complex.sq_norm]; exact pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hdisc_g' : (k2 + k3 * R ^ 2) ^ 2 ≤ 4 * (k1 + k2 * R ^ 2 + k3 * (R ^ 2) ^ 2) * k3 := by
    nlinarith [hdisc_g]
  have hb := cubic_tight_pos k1 k2 k3 (R ^ 2) hc hdisc_h hdisc_g' (Complex.normSq z) hu0 huU
  have heq : radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z
      = k1 * Complex.normSq z + k2 * (Complex.normSq z) ^ 2 + k3 * (Complex.normSq z) ^ 3 := rfl
  rw [heq, abs_of_nonneg hb.1]
  unfold RfacDevUBTightPos
  rw [abs_of_nonneg (by nlinarith [hb.1, hb.2] : (0:ℝ) ≤ k1*R^2+k2*R^4+k3*R^6)]
  nlinarith [hb.2]

theorem radial_tight_lipschitz_pos (k1 k2 k3 R : ℝ) (hR : 0 ≤ R)
    (hdisc_psi : k2 ^ 2 ≤ 3 * k1 * k3) (hc : 0 < k3)
    (a b : ℂ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    |radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a - radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) b|
      ≤ RfacLTightPos k1 k2 k3 R * ‖a - b‖ := by
  have hua0 : 0 ≤ Complex.normSq a := Complex.normSq_nonneg a
  have huaU : Complex.normSq a ≤ R ^ 2 := by
    rw [← Complex.sq_norm]; exact pow_le_pow_left₀ (norm_nonneg a) ha 2
  have hub0 : 0 ≤ Complex.normSq b := Complex.normSq_nonneg b
  have hubU : Complex.normSq b ≤ R ^ 2 := by
    rw [← Complex.sq_norm]; exact pow_le_pow_left₀ (norm_nonneg b) hb 2
  have hkbound' := k_bound_pos k1 k2 k3 (R ^ 2) hc (by positivity) hdisc_psi
    (Complex.normSq a) (Complex.normSq b) hua0 huaU hub0 hubU
  have hkbound : |k1 + k2 * (Complex.normSq a + Complex.normSq b)
      + k3 * (Complex.normSq a ^ 2 + Complex.normSq a * Complex.normSq b + Complex.normSq b ^ 2)|
      ≤ max k1 (k1 + 2 * k2 * R ^ 2 + 4 * k3 * R ^ 4) := by
    have heq3 : max k1 (k1 + 2 * k2 * R ^ 2 + 4 * k3 * (R ^ 2) ^ 2)
        = max k1 (k1 + 2 * k2 * R ^ 2 + 4 * k3 * R ^ 4) := by ring_nf
    rw [heq3] at hkbound'
    exact hkbound'
  have heqdiff : radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a - radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) b
      = (Complex.normSq a - Complex.normSq b)
        * (k1 + k2 * (Complex.normSq a + Complex.normSq b)
            + k3 * (Complex.normSq a ^ 2 + Complex.normSq a * Complex.normSq b + Complex.normSq b ^ 2)) := by
    show (k1 * Complex.normSq a + k2 * (Complex.normSq a) ^ 2 + k3 * (Complex.normSq a) ^ 3)
        - (k1 * Complex.normSq b + k2 * (Complex.normSq b) ^ 2 + k3 * (Complex.normSq b) ^ 3) = _
    ring
  rw [heqdiff, abs_mul]
  have hns_lip := normSq_lipschitz R a b ha hb
  calc |Complex.normSq a - Complex.normSq b|
      * |k1 + k2 * (Complex.normSq a + Complex.normSq b)
          + k3 * (Complex.normSq a ^ 2 + Complex.normSq a * Complex.normSq b + Complex.normSq b ^ 2)|
      ≤ (2 * R * ‖a - b‖) * max k1 (k1 + 2 * k2 * R ^ 2 + 4 * k3 * R ^ 4) := by
        apply mul_le_mul hns_lip hkbound (abs_nonneg _) (by positivity)
    _ = RfacLTightPos k1 k2 k3 R * ‖a - b‖ := by unfold RfacLTightPos; ring

/-─────────────────────────────────────────────────────────────────────────────
  Pert-level bounds: Pert θ z = (Rfac θ z - 1)•z + Tang θ z, and when
  k4=k5=k6=0, `Rfac θ z - 1 = radial (numCoeffs θ) z` exactly (Dden θ z ≡ 1).
  Tang/M/L are REUSED unchanged (tangential part is not tightened here).
─────────────────────────────────────────────────────────────────────────────-/

theorem Pert_eq_nodenom (k1 k2 k3 p1 p2 : ℝ) (z : ℂ) :
    Pert (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z
      = (radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z : ℝ) • z + Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z := by
  unfold Pert Rfac Nnum Dden radial RCoeffsOf numCoeffs denCoeffs
  congr 2
  ring

theorem Pert_bounded_tight_pos (k1 k2 k3 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (hdisc_h : k2 ^ 2 ≤ 4 * k1 * k3)
    (hdisc_g : (k2 + k3 * R ^ 2) ^ 2 ≤ 4 * (k1 + k2 * R ^ 2 + k3 * R ^ 4) * k3)
    (hc : 0 < k3) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖Pert (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z‖ ≤ MPertTightPos k1 k2 k3 p1 p2 R := by
  rw [Pert_eq_nodenom]
  have h1 : ‖(radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z : ℝ) • z‖
      = |radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z| * ‖z‖ := smul_norm _ _
  have h2 := radial_tight_bound_pos k1 k2 k3 R hR hdisc_h hdisc_g hc z hz
  have h3 : ‖Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z‖ ≤ M (⟨0, 0, 0, p1, p2⟩ : Coeffs) R := by
    have := Tang_bounded (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) R hR z hz
    have heq : tangCoeffs (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) = (⟨0, 0, 0, p1, p2⟩ : Coeffs) := by
      rfl
    rwa [heq] at this
  have h2nn : 0 ≤ RfacDevUBTightPos k1 k2 k3 R := abs_nonneg _
  unfold MPertTightPos
  calc ‖(radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z : ℝ) • z + Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z‖
      ≤ ‖(radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z : ℝ) • z‖ + ‖Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z‖ :=
        norm_add_le _ _
    _ = |radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z| * ‖z‖ + ‖Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z‖ := by
        rw [h1]
    _ ≤ RfacDevUBTightPos k1 k2 k3 R * R + M (⟨0, 0, 0, p1, p2⟩ : Coeffs) R := by gcongr

theorem Pert_lipschitz_tight_pos (k1 k2 k3 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (hdisc_h : k2 ^ 2 ≤ 4 * k1 * k3)
    (hdisc_g : (k2 + k3 * R ^ 2) ^ 2 ≤ 4 * (k1 + k2 * R ^ 2 + k3 * R ^ 4) * k3)
    (hdisc_psi : k2 ^ 2 ≤ 3 * k1 * k3) (hc : 0 < k3)
    (a b : ℂ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖Pert (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) a - Pert (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) b‖
      ≤ LPertTightPos k1 k2 k3 p1 p2 R * ‖a - b‖ := by
  rw [Pert_eq_nodenom, Pert_eq_nodenom]
  have hRlip := radial_tight_lipschitz_pos k1 k2 k3 R hR hdisc_psi hc a b ha hb
  have hRa : |radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a| ≤ RfacDevUBTightPos k1 k2 k3 R :=
    radial_tight_bound_pos k1 k2 k3 R hR hdisc_h hdisc_g hc a ha
  have hTlip : ‖Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) a - Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) b‖
      ≤ L (⟨0, 0, 0, p1, p2⟩ : Coeffs) R * ‖a - b‖ := by
    have := Tang_lipschitz (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) R hR a b ha hb
    have heq : tangCoeffs (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) = (⟨0, 0, 0, p1, p2⟩ : Coeffs) := by
      rfl
    rwa [heq] at this
  have hgoaleq : ((radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a : ℝ) • a
        + Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) a)
      - ((radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) b : ℝ) • b + Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) b)
      = (radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a : ℝ) • (a - b)
        + (radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a - radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) b : ℝ) • b
        + (Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) a - Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) b) := by
    module
  rw [hgoaleq]
  have hstep1 : ‖(radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a : ℝ) • (a - b)
        + (radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a - radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) b : ℝ) • b
        + (Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) a - Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) b)‖
      ≤ ‖(radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a : ℝ) • (a - b)‖
        + ‖(radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a - radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) b : ℝ) • b‖
        + ‖Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) a - Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) b‖ := by
    have h1 := norm_add_le ((radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a : ℝ) • (a - b)
      + (radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a - radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) b : ℝ) • b)
      (Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) a - Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) b)
    have h2 := norm_add_le ((radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a : ℝ) • (a - b))
      ((radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a - radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) b : ℝ) • b)
    linarith
  have hnorms : ‖(radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a : ℝ) • (a - b)‖
        + ‖(radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a - radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) b : ℝ) • b‖
        + ‖Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) a - Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) b‖
      = |radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a| * ‖a - b‖
        + |radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a - radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) b| * ‖b‖
        + ‖Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) a - Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) b‖ := by
    rw [smul_norm, smul_norm]
  have hk1nn : 0 ≤ k1 := by nlinarith [sq_nonneg k2, hdisc_psi, hc]
  have hRfacLnn : 0 ≤ RfacLTightPos k1 k2 k3 R := by
    unfold RfacLTightPos
    have : 0 ≤ max k1 (k1 + 2 * k2 * R ^ 2 + 4 * k3 * R ^ 4) := le_trans hk1nn (le_max_left _ _)
    positivity
  have hfinal : |radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a| * ‖a - b‖
        + |radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a - radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) b| * ‖b‖
        + ‖Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) a - Tang (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) b‖
      ≤ RfacDevUBTightPos k1 k2 k3 R * ‖a - b‖ + (RfacLTightPos k1 k2 k3 R * ‖a - b‖) * R
        + L (⟨0, 0, 0, p1, p2⟩ : Coeffs) R * ‖a - b‖ := by
    gcongr
  have heq2 : RfacDevUBTightPos k1 k2 k3 R * ‖a - b‖ + (RfacLTightPos k1 k2 k3 R * ‖a - b‖) * R
      + L (⟨0, 0, 0, p1, p2⟩ : Coeffs) R * ‖a - b‖
      = LPertTightPos k1 k2 k3 p1 p2 R * ‖a - b‖ := by unfold LPertTightPos; ring
  linarith [hstep1, hnorms, hfinal, heq2]

/-─────────────────────────────────────────────────────────────────────────────
  Banach fixed-point existence/uniqueness, mirroring
  RationalDistortionInjectivity.lean's RDist_exists_unique_preimage exactly,
  substituting MPertTightPos/LPertTightPos for MPert/LPert and
  Pert_bounded_tight_pos/Pert_lipschitz_tight_pos for Pert_bounded/
  Pert_lipschitz. RDist itself (and RDist_eq_add_Pert) is REUSED unchanged.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def inverseStepRTight (k1 k2 k3 p1 p2 : ℝ) (y z : ℂ) : ℂ :=
  y - Pert (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z

theorem inverseStepRTight_maps_disk (k1 k2 k3 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (hdisc_h : k2 ^ 2 ≤ 4 * k1 * k3)
    (hdisc_g : (k2 + k3 * R ^ 2) ^ 2 ≤ 4 * (k1 + k2 * R ^ 2 + k3 * R ^ 4) * k3)
    (hc : 0 < k3) (y z : ℂ)
    (hy : ‖y‖ + MPertTightPos k1 k2 k3 p1 p2 R ≤ R) (hz : ‖z‖ ≤ R) :
    ‖inverseStepRTight k1 k2 k3 p1 p2 y z‖ ≤ R := by
  unfold inverseStepRTight
  have hp := Pert_bounded_tight_pos k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hc z hz
  calc ‖y - Pert (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z‖
      ≤ ‖y‖ + ‖Pert (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z‖ := norm_sub_le _ _
    _ ≤ ‖y‖ + MPertTightPos k1 k2 k3 p1 p2 R := by gcongr
    _ ≤ R := hy

theorem inverseStepRTight_lipschitz (k1 k2 k3 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (hdisc_h : k2 ^ 2 ≤ 4 * k1 * k3)
    (hdisc_g : (k2 + k3 * R ^ 2) ^ 2 ≤ 4 * (k1 + k2 * R ^ 2 + k3 * R ^ 4) * k3)
    (hdisc_psi : k2 ^ 2 ≤ 3 * k1 * k3) (hc : 0 < k3)
    (y a b : ℂ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖inverseStepRTight k1 k2 k3 p1 p2 y a - inverseStepRTight k1 k2 k3 p1 p2 y b‖
      ≤ LPertTightPos k1 k2 k3 p1 p2 R * ‖a - b‖ := by
  unfold inverseStepRTight
  have heq : (y - Pert (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) a) - (y - Pert (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) b)
      = -(Pert (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) a - Pert (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) b) := by abel
  rw [heq, norm_neg]
  exact Pert_lipschitz_tight_pos k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc a b ha hb

theorem MPertTightPos_nonneg (k1 k2 k3 p1 p2 R : ℝ) (hR : 0 ≤ R) : 0 ≤ MPertTightPos k1 k2 k3 p1 p2 R := by
  have h1 : 0 ≤ RfacDevUBTightPos k1 k2 k3 R := abs_nonneg _
  have h2 : 0 ≤ M (⟨0, 0, 0, p1, p2⟩ : Coeffs) R := by unfold M; positivity
  unfold MPertTightPos
  have : 0 ≤ RfacDevUBTightPos k1 k2 k3 R * R := mul_nonneg h1 hR
  linarith

theorem LPertTightPos_nonneg (k1 k2 k3 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (hdisc_psi : k2 ^ 2 ≤ 3 * k1 * k3) (hc : 0 < k3) :
    0 ≤ LPertTightPos k1 k2 k3 p1 p2 R := by
  have h1 : 0 ≤ RfacDevUBTightPos k1 k2 k3 R := abs_nonneg _
  have hk1nn : 0 ≤ k1 := by nlinarith [sq_nonneg k2, hdisc_psi, hc]
  have h2 : 0 ≤ RfacLTightPos k1 k2 k3 R := by
    unfold RfacLTightPos
    have : 0 ≤ max k1 (k1 + 2 * k2 * R ^ 2 + 4 * k3 * R ^ 4) := le_trans hk1nn (le_max_left _ _)
    positivity
  have h3 : 0 ≤ L (⟨0, 0, 0, p1, p2⟩ : Coeffs) R := by unfold L; positivity
  unfold LPertTightPos
  have : 0 ≤ RfacLTightPos k1 k2 k3 R * R := mul_nonneg h2 hR
  linarith

theorem RDist_exists_unique_preimage_tight_pos
    (k1 k2 k3 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (hdisc_h : k2 ^ 2 ≤ 4 * k1 * k3)
    (hdisc_g : (k2 + k3 * R ^ 2) ^ 2 ≤ 4 * (k1 + k2 * R ^ 2 + k3 * R ^ 4) * k3)
    (hdisc_psi : k2 ^ 2 ≤ 3 * k1 * k3) (hc : 0 < k3)
    (hcontract : LPertTightPos k1 k2 k3 p1 p2 R < 1)
    (y : ℂ) (hy : ‖y‖ + MPertTightPos k1 k2 k3 p1 p2 R ≤ R) :
    ∃! z : ℂ, ‖z‖ ≤ R ∧ RDist (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z = y := by
  set θ := RCoeffsOf k1 k2 k3 0 0 0 p1 p2 with hθdef
  have hM_nonneg : (0:ℝ) ≤ MPertTightPos k1 k2 k3 p1 p2 R := MPertTightPos_nonneg k1 k2 k3 p1 p2 R hR
  have hyR : ‖y‖ ≤ R := by linarith
  have hiff : ∀ z : ℂ, inverseStepRTight k1 k2 k3 p1 p2 y z = z ↔ RDist θ z = y := by
    intro z
    rw [RDist_eq_add_Pert θ z]
    unfold inverseStepRTight
    rw [hθdef]
    constructor
    · intro h; linear_combination -h
    · intro h; linear_combination -h
  set s : Set ℂ := {z : ℂ | ‖z‖ ≤ R} with hs_def
  have hclosed : IsClosed s := by
    have hball : s = Metric.closedBall (0 : ℂ) R := by
      ext z; simp [hs_def, Metric.mem_closedBall, dist_eq_norm]
    rw [hball]; exact Metric.isClosed_closedBall
  have hcomplete : IsComplete s := hclosed.isComplete
  have hMapsTo : Set.MapsTo (inverseStepRTight k1 k2 k3 p1 p2 y) s s := fun z hz =>
    inverseStepRTight_maps_disk k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hc y z hy hz
  set K : NNReal := (LPertTightPos k1 k2 k3 p1 p2 R).toNNReal with hK_def
  have hK0 : (0:ℝ) ≤ LPertTightPos k1 k2 k3 p1 p2 R := LPertTightPos_nonneg k1 k2 k3 p1 p2 R hR hdisc_psi hc
  have hKcoe : (K : ℝ) = LPertTightPos k1 k2 k3 p1 p2 R := Real.coe_toNNReal _ hK0
  have hKlt1 : K < 1 := by
    rw [← NNReal.coe_lt_coe, hKcoe]; simpa using hcontract
  have hLip : LipschitzWith K (hMapsTo.restrict (inverseStepRTight k1 k2 k3 p1 p2 y) s s) := by
    apply LipschitzWith.of_dist_le_mul
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Set.MapsTo.restrict, Subtype.dist_eq]
    rw [hKcoe]
    have := inverseStepRTight_lipschitz k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc y a b ha hb
    simpa [dist_eq_norm] using this
  have hContract : ContractingWith K (hMapsTo.restrict (inverseStepRTight k1 k2 k3 p1 p2 y) s s) := ⟨hKlt1, hLip⟩
  have hys : y ∈ s := hyR
  have hedist : edist y (inverseStepRTight k1 k2 k3 p1 p2 y y) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨z, hzs, hfz, _, _⟩ := hContract.exists_fixedPoint' hcomplete hMapsTo hys hedist
  refine ⟨z, ⟨hzs, (hiff z).mp hfz⟩, ?_⟩
  rintro w ⟨hws, hDw⟩
  have hfw : inverseStepRTight k1 k2 k3 p1 p2 y w = w := (hiff w).mpr hDw
  have hzw : (⟨z, hzs⟩ : s) = (⟨w, hws⟩ : s) := by
    apply hContract.fixedPoint_unique' (x := (⟨z, hzs⟩ : s)) (y := (⟨w, hws⟩ : s))
    · show (hMapsTo.restrict (inverseStepRTight k1 k2 k3 p1 p2 y) s s) ⟨z, hzs⟩ = ⟨z, hzs⟩
      exact Subtype.ext hfz
    · show (hMapsTo.restrict (inverseStepRTight k1 k2 k3 p1 p2 y) s s) ⟨w, hws⟩ = ⟨w, hws⟩
      exact Subtype.ext hfw
  exact (congrArg Subtype.val hzw).symm

/-─────────────────────────────────────────────────────────────────────────────
  Bridge to CVmap/SensorPoint, mirroring RationalDistortionBridge.lean's
  RDistInv/RDist_inverse_invOn/CVmap_inverse_invOn exactly, with the tight
  constants/theorems in place of the originals. `CVmap_eq_RDist` and
  `toComplexEquiv`/`conjugate_invOn` are REUSED unchanged.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def RDistInvTight (k1 k2 k3 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (hdisc_h : k2 ^ 2 ≤ 4 * k1 * k3)
    (hdisc_g : (k2 + k3 * R ^ 2) ^ 2 ≤ 4 * (k1 + k2 * R ^ 2 + k3 * R ^ 4) * k3)
    (hdisc_psi : k2 ^ 2 ≤ 3 * k1 * k3) (hc : 0 < k3)
    (hcontract : LPertTightPos k1 k2 k3 p1 p2 R < 1) (y : ℂ) : ℂ :=
  open Classical in
  if h : ‖y‖ + MPertTightPos k1 k2 k3 p1 p2 R ≤ R then
    (RDist_exists_unique_preimage_tight_pos k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc
      hcontract y h).exists.choose
  else 0

theorem RDist_inverse_invOn_tight (k1 k2 k3 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (hdisc_h : k2 ^ 2 ≤ 4 * k1 * k3)
    (hdisc_g : (k2 + k3 * R ^ 2) ^ 2 ≤ 4 * (k1 + k2 * R ^ 2 + k3 * R ^ 4) * k3)
    (hdisc_psi : k2 ^ 2 ≤ 3 * k1 * k3) (hc : 0 < k3)
    (hcontract : LPertTightPos k1 k2 k3 p1 p2 R < 1) :
    Set.InvOn (RDistInvTight k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc hcontract)
      (RDist (RCoeffsOf k1 k2 k3 0 0 0 p1 p2))
      {z : ℂ | ‖z‖ ≤ R ∧ ‖RDist (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z‖ + MPertTightPos k1 k2 k3 p1 p2 R ≤ R}
      {y : ℂ | ‖y‖ + MPertTightPos k1 k2 k3 p1 p2 R ≤ R} := by
  constructor
  · intro z hz
    obtain ⟨hzR, hyR⟩ := hz
    have huniq := RDist_exists_unique_preimage_tight_pos k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc
      hcontract (RDist (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z) hyR
    have hchoose_spec := huniq.exists.choose_spec
    have hval : RDistInvTight k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc hcontract
        (RDist (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z) = huniq.exists.choose := by
      show (if h : ‖RDist (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z‖ + MPertTightPos k1 k2 k3 p1 p2 R ≤ R then
              (RDist_exists_unique_preimage_tight_pos k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc
                hcontract (RDist (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z) h).exists.choose
            else 0) = huniq.exists.choose
      rw [dif_pos hyR]
    rw [hval]
    exact huniq.unique hchoose_spec ⟨hzR, rfl⟩
  · intro y hy
    have hy' : ‖y‖ + MPertTightPos k1 k2 k3 p1 p2 R ≤ R := hy
    have hval : RDistInvTight k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc hcontract y
        = (RDist_exists_unique_preimage_tight_pos k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc
            hcontract y hy').exists.choose := by
      show (if h : ‖y‖ + MPertTightPos k1 k2 k3 p1 p2 R ≤ R then
              (RDist_exists_unique_preimage_tight_pos k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc
                hcontract y h).exists.choose
            else 0) = (RDist_exists_unique_preimage_tight_pos k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc
              hcontract y hy').exists.choose
      rw [dif_pos hy']
    rw [hval]
    exact (RDist_exists_unique_preimage_tight_pos k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc
      hcontract y hy').exists.choose_spec.2

theorem CVmap_inverse_invOn_tight
    (k1 k2 k3 p1 p2 : ℝ)
    (hden : ∀ x' y' : ℝ, 1 + (0:ℝ) * (x' ^ 2 + y' ^ 2) + (0:ℝ) * (x' ^ 2 + y' ^ 2) ^ 2
              + (0:ℝ) * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0)
    (R : ℝ) (hR : 0 ≤ R)
    (hdisc_h : k2 ^ 2 ≤ 4 * k1 * k3)
    (hdisc_g : (k2 + k3 * R ^ 2) ^ 2 ≤ 4 * (k1 + k2 * R ^ 2 + k3 * R ^ 4) * k3)
    (hdisc_psi : k2 ^ 2 ≤ 3 * k1 * k3) (hc : 0 < k3)
    (hcontract : LPertTightPos k1 k2 k3 p1 p2 R < 1) :
    Set.InvOn
      (toComplexEquiv.symm ∘
        RDistInvTight k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc hcontract ∘ toComplexEquiv)
      (CVmap k1 k2 k3 0 0 0 p1 p2 hden)
      (toComplexEquiv.symm ''
        {z : ℂ | ‖z‖ ≤ R ∧ ‖RDist (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) z‖
                    + MPertTightPos k1 k2 k3 p1 p2 R ≤ R})
      (toComplexEquiv.symm '' {y : ℂ | ‖y‖ + MPertTightPos k1 k2 k3 p1 p2 R ≤ R}) := by
  set θ := RCoeffsOf k1 k2 k3 0 0 0 p1 p2 with hθ
  have hconj : ∀ x : ℂ,
      CVmap k1 k2 k3 0 0 0 p1 p2 hden (toComplexEquiv.symm x) = toComplexEquiv.symm (RDist θ x) := by
    intro x
    have h := CVmap_eq_RDist k1 k2 k3 0 0 0 p1 p2 hden (toComplexEquiv.symm x)
    rw [toComplexEquiv.apply_symm_apply] at h
    have h2 := congrArg toComplexEquiv.symm h
    rwa [Equiv.symm_apply_apply] at h2
  have hmain := conjugate_invOn toComplexEquiv.symm (RDist θ)
    (RDistInvTight k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc hcontract)
    (CVmap k1 k2 k3 0 0 0 p1 p2 hden)
    {z : ℂ | ‖z‖ ≤ R ∧ ‖RDist θ z‖ + MPertTightPos k1 k2 k3 p1 p2 R ≤ R}
    {y : ℂ | ‖y‖ + MPertTightPos k1 k2 k3 p1 p2 R ≤ R}
    hconj (RDist_inverse_invOn_tight k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc hcontract)
  simpa [Equiv.symm_symm] using hmain

