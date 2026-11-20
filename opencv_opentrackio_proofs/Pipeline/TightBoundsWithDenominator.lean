/-
  Pipeline/TightBoundsWithDenominator.lean

  Specializes the signed-cubic tightening (Pipeline/SignedCubicBounds.lean) to
  the MONOTONE-NEGATIVE case (`cubic_tight_neg`/`k_bound_neg`) with a GENUINE
  nonzero rational denominator — the Azure Kinect DK calibration
  (audit/REAL_CALIBRATION_VALIDATION.md), where both the numerator and
  denominator polynomials are negative-definite-on-the-relevant-range rather
  than sign-definite-everywhere (so Pipeline/TightBoundsNoDenominator.lean's
  discriminant route does not apply — see
  audit/IMPROVED_REAL_CALIBRATION_BOUNDS.md §3 for the numeric comparison).

  Requires the full quotient-rule combination (mirroring
  Pipeline/RationalRadialBounds.lean's `Rfac_bounded`/`Rfac_lipschitz` proofs
  exactly, substituting the tight Nnum/Dden bounds for the crude
  Mrad/Lrad-based ones), since the denominator here is NOT identically 1.

  Reuses, unchanged: `M`/`L`/`Tang_bounded`/`Tang_lipschitz`
  (InverseApproximation.lean/RationalDistortionBounds.lean),
  `normSq_lipschitz`, `cubic_tight_neg`/`k_bound_neg`
  (SignedCubicBounds.lean), `CVmap_eq_RDist`/`toComplexEquiv`
  (RationalDistortionBridge.lean), `conjugate_invOn` (InverseConjugacy.lean).

  Does not modify any existing file, weaken any existing theorem, or
  introduce axioms.
-/

import Pipeline.SignedCubicBounds
import Pipeline.RationalDistortionBridge
import Pipeline.RationalRadialBounds

/-─────────────────────────────────────────────────────────────────────────────
  Tight numerator/denominator bounds (monotone-negative case).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def MtightNeg (a b c R : ℝ) : ℝ := |a * R ^ 2 + b * R ^ 4 + c * R ^ 6|

noncomputable def LtightNegU (a b c R : ℝ) : ℝ := |a + 2 * b * R ^ 2 + 3 * c * R ^ 4|

noncomputable def LtightNeg (a b c R : ℝ) : ℝ := 2 * R * LtightNegU a b c R

theorem radial_tight_bound_neg (a b c R : ℝ) (hR : 0 ≤ R)
    (ha : a ≤ 0) (hmono : b + 3 * c * R ^ 2 ≤ 0) (hc : 0 < c)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    |radial (⟨a, b, c, 0, 0⟩ : Coeffs) z| ≤ MtightNeg a b c R := by
  have hu0 : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
  have huU : Complex.normSq z ≤ R ^ 2 := by
    rw [← Complex.sq_norm]; exact pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hbd := cubic_tight_neg a b c (R ^ 2) hc ha hmono (Complex.normSq z) hu0 huU
  have heq : radial (⟨a, b, c, 0, 0⟩ : Coeffs) z
      = a * Complex.normSq z + b * (Complex.normSq z) ^ 2 + c * (Complex.normSq z) ^ 3 := rfl
  rw [heq, abs_of_nonpos hbd.2]
  unfold MtightNeg
  rw [abs_of_nonpos (by nlinarith [hbd.1, hbd.2] : a * R ^ 2 + b * R ^ 4 + c * R ^ 6 ≤ 0)]
  nlinarith [hbd.1]

theorem radial_tight_lipschitz_neg (a b c R : ℝ) (hR : 0 ≤ R)
    (ha : a ≤ 0) (hmono : b + 4 * c * R ^ 2 ≤ 0) (hc : 0 < c)
    (u1 u2 : ℂ) (h1 : ‖u1‖ ≤ R) (h2 : ‖u2‖ ≤ R) :
    |radial (⟨a, b, c, 0, 0⟩ : Coeffs) u1 - radial (⟨a, b, c, 0, 0⟩ : Coeffs) u2|
      ≤ LtightNeg a b c R * ‖u1 - u2‖ := by
  have hua0 : 0 ≤ Complex.normSq u1 := Complex.normSq_nonneg u1
  have huaU : Complex.normSq u1 ≤ R ^ 2 := by
    rw [← Complex.sq_norm]; exact pow_le_pow_left₀ (norm_nonneg u1) h1 2
  have hub0 : 0 ≤ Complex.normSq u2 := Complex.normSq_nonneg u2
  have hubU : Complex.normSq u2 ≤ R ^ 2 := by
    rw [← Complex.sq_norm]; exact pow_le_pow_left₀ (norm_nonneg u2) h2 2
  have hkbound := k_bound_neg a b c (R ^ 2) hc (by positivity) ha hmono
    (Complex.normSq u1) (Complex.normSq u2) hua0 huaU hub0 hubU
  have heqdiff : radial (⟨a, b, c, 0, 0⟩ : Coeffs) u1 - radial (⟨a, b, c, 0, 0⟩ : Coeffs) u2
      = (Complex.normSq u1 - Complex.normSq u2)
        * (a + b * (Complex.normSq u1 + Complex.normSq u2)
            + c * (Complex.normSq u1 ^ 2 + Complex.normSq u1 * Complex.normSq u2 + Complex.normSq u2 ^ 2)) := by
    show (a * Complex.normSq u1 + b * (Complex.normSq u1) ^ 2 + c * (Complex.normSq u1) ^ 3)
        - (a * Complex.normSq u2 + b * (Complex.normSq u2) ^ 2 + c * (Complex.normSq u2) ^ 3) = _
    ring
  rw [heqdiff, abs_mul]
  have hns_lip := normSq_lipschitz R u1 u2 h1 h2
  have hkbound' : |a + b * (Complex.normSq u1 + Complex.normSq u2)
      + c * (Complex.normSq u1 ^ 2 + Complex.normSq u1 * Complex.normSq u2 + Complex.normSq u2 ^ 2)|
      ≤ LtightNegU a b c R := by
    unfold LtightNegU
    have heq3 : a + 2 * b * R ^ 2 + 3 * c * (R ^ 2) ^ 2 = a + 2 * b * R ^ 2 + 3 * c * R ^ 4 := by ring
    rw [show |a + 2 * b * R ^ 2 + 3 * c * R ^ 4| = |a + 2 * b * R ^ 2 + 3 * c * (R ^ 2) ^ 2| from by rw [heq3]]
    exact hkbound
  calc |Complex.normSq u1 - Complex.normSq u2|
      * |a + b * (Complex.normSq u1 + Complex.normSq u2)
          + c * (Complex.normSq u1 ^ 2 + Complex.normSq u1 * Complex.normSq u2 + Complex.normSq u2 ^ 2)|
      ≤ (2 * R * ‖u1 - u2‖) * LtightNegU a b c R := by
        apply mul_le_mul hns_lip hkbound' (abs_nonneg _) (by positivity)
    _ = LtightNeg a b c R * ‖u1 - u2‖ := by unfold LtightNeg; ring

/-─────────────────────────────────────────────────────────────────────────────
  Denominator safety, mirroring RationalRadialBounds.lean's `denom_pos`/
  `denom_ge` with the tight margin `MtightNeg(k4,k5,k6,R)` in place of
  `denomMargin`.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def denomLBTightNeg (k4 k5 k6 R : ℝ) : ℝ := 1 - MtightNeg k4 k5 k6 R

theorem Dden_tight_ge (k4 k5 k6 R : ℝ) (hR : 0 ≤ R)
    (ha : k4 ≤ 0) (hmono : k5 + 3 * k6 * R ^ 2 ≤ 0) (hc : 0 < k6)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    denomLBTightNeg k4 k5 k6 R ≤ 1 + radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) z := by
  have hb := radial_tight_bound_neg k4 k5 k6 R hR ha hmono hc z hz
  have h2 := (abs_le.mp hb).1
  unfold denomLBTightNeg; linarith

theorem Dden_tight_pos (k4 k5 k6 R : ℝ) (hR : 0 ≤ R)
    (ha : k4 ≤ 0) (hmono : k5 + 3 * k6 * R ^ 2 ≤ 0) (hc : 0 < k6)
    (hsafe : MtightNeg k4 k5 k6 R < 1)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    0 < 1 + radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) z := by
  have h := Dden_tight_ge k4 k5 k6 R hR ha hmono hc z hz
  unfold denomLBTightNeg at h; linarith

/-─────────────────────────────────────────────────────────────────────────────
  Rfac-level bound/Lipschitz, via the EXISTING `Nnum`/`Dden`/`Rfac`
  (RationalRadialBounds.lean, applied to θ := RCoeffsOf k1..k6 p1 p2 — so
  `Nnum θ z = 1 + radial (numCoeffs θ) z` and `numCoeffs θ = ⟨k1,k2,k3,0,0⟩`
  DEFINITIONALLY, matching radial_tight_bound_neg's shape exactly), mirroring
  RationalRadialBounds.lean's `Rfac_bounded`/`Rfac_lipschitz` quotient-rule
  proof structure with `MtightNeg`/`LtightNeg` substituted for `Mrad`/`Lrad`
  and the UPPER bound `1` for `NnumUB`/`DdenUB` (valid here since
  Nnum,Dden ∈ [1+f(U), 1] ⊆ [-1,1] when f(U) ≤ 0).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def RfacDevUBTightNeg (k1 k2 k3 k4 k5 k6 R : ℝ) : ℝ :=
  (MtightNeg k1 k2 k3 R + MtightNeg k4 k5 k6 R) / denomLBTightNeg k4 k5 k6 R

noncomputable def RfacLTightNeg (k1 k2 k3 k4 k5 k6 R : ℝ) : ℝ :=
  (LtightNeg k4 k5 k6 R + LtightNeg k1 k2 k3 R) / (denomLBTightNeg k4 k5 k6 R) ^ 2

theorem Nnum_tight_bound_neg (k1 k2 k3 R : ℝ) (hR : 0 ≤ R) (ha : k1 ≤ 0)
    (hmono : k2 + 3 * k3 * R ^ 2 ≤ 0) (hc : 0 < k3)
    (hge2 : (-2:ℝ) ≤ k1 * R ^ 2 + k2 * R ^ 4 + k3 * R ^ 6)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    |Nnum (RCoeffsOf k1 k2 k3 0 0 0 0 0) z| ≤ 1 := by
  have hbd := cubic_tight_neg k1 k2 k3 (R ^ 2) hc ha hmono (Complex.normSq z)
    (Complex.normSq_nonneg z) (by rw [← Complex.sq_norm]; exact pow_le_pow_left₀ (norm_nonneg z) hz 2)
  have heq : Nnum (RCoeffsOf k1 k2 k3 0 0 0 0 0) z = 1 + radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z := rfl
  rw [heq]
  have heqr : radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z
      = k1 * Complex.normSq z + k2 * (Complex.normSq z) ^ 2 + k3 * (Complex.normSq z) ^ 3 := rfl
  rw [heqr, abs_le]
  have hUeq : k1 * R ^ 2 + k2 * (R ^ 2) ^ 2 + k3 * (R ^ 2) ^ 3 = k1 * R ^ 2 + k2 * R ^ 4 + k3 * R ^ 6 := by ring
  constructor <;> nlinarith [hbd.1, hbd.2, hge2, hUeq]

theorem Dden_tight_bound_neg (k4 k5 k6 R : ℝ) (hR : 0 ≤ R) (ha : k4 ≤ 0)
    (hmono : k5 + 3 * k6 * R ^ 2 ≤ 0) (hc : 0 < k6)
    (hge2 : (-2:ℝ) ≤ k4 * R ^ 2 + k5 * R ^ 4 + k6 * R ^ 6)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    |Dden (RCoeffsOf 0 0 0 k4 k5 k6 0 0) z| ≤ 1 := by
  have hbd := cubic_tight_neg k4 k5 k6 (R ^ 2) hc ha hmono (Complex.normSq z)
    (Complex.normSq_nonneg z) (by rw [← Complex.sq_norm]; exact pow_le_pow_left₀ (norm_nonneg z) hz 2)
  have heq : Dden (RCoeffsOf 0 0 0 k4 k5 k6 0 0) z = 1 + radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) z := rfl
  rw [heq]
  have heqr : radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) z
      = k4 * Complex.normSq z + k5 * (Complex.normSq z) ^ 2 + k6 * (Complex.normSq z) ^ 3 := rfl
  rw [heqr, abs_le]
  have hUeq : k4 * R ^ 2 + k5 * (R ^ 2) ^ 2 + k6 * (R ^ 2) ^ 3 = k4 * R ^ 2 + k5 * R ^ 4 + k6 * R ^ 6 := by ring
  constructor <;> nlinarith [hbd.1, hbd.2, hge2, hUeq]

theorem Rfac_tight_bounded_neg (k1 k2 k3 k4 k5 k6 R : ℝ) (hR : 0 ≤ R)
    (ha1 : k1 ≤ 0) (hmono1 : k2 + 3 * k3 * R ^ 2 ≤ 0) (hc1 : 0 < k3)
    (hge2_1 : (-2:ℝ) ≤ k1 * R ^ 2 + k2 * R ^ 4 + k3 * R ^ 6)
    (ha4 : k4 ≤ 0) (hmono4 : k5 + 3 * k6 * R ^ 2 ≤ 0) (hc4 : 0 < k6)
    (hge2_4 : (-2:ℝ) ≤ k4 * R ^ 2 + k5 * R ^ 4 + k6 * R ^ 6)
    (hsafe : MtightNeg k4 k5 k6 R < 1) (z : ℂ) (hz : ‖z‖ ≤ R) :
    |Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z| ≤ 1 / denomLBTightNeg k4 k5 k6 R := by
  have hDpos : 0 < Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z := by
    have : Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z = 1 + radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) z := rfl
    rw [this]; exact Dden_tight_pos k4 k5 k6 R hR ha4 hmono4 hc4 hsafe z hz
  have hDge : denomLBTightNeg k4 k5 k6 R ≤ Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z := by
    have heq : Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z = 1 + radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) z := rfl
    rw [heq]; exact Dden_tight_ge k4 k5 k6 R hR ha4 hmono4 hc4 z hz
  have hNle : |Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z| ≤ 1 := by
    have heqN : Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z = Nnum (RCoeffsOf k1 k2 k3 0 0 0 0 0) z := rfl
    rw [heqN]
    exact Nnum_tight_bound_neg k1 k2 k3 R hR ha1 hmono1 hc1 hge2_1 z hz
  have hLBpos : 0 < denomLBTightNeg k4 k5 k6 R := by unfold denomLBTightNeg; linarith [hsafe]
  unfold Rfac
  rw [abs_div, abs_of_pos hDpos]
  calc |Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z| / Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z
      ≤ |Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z| / denomLBTightNeg k4 k5 k6 R :=
        div_le_div_of_nonneg_left (abs_nonneg _) hLBpos hDge
    _ ≤ 1 / denomLBTightNeg k4 k5 k6 R := by
        apply div_le_div_of_nonneg_right hNle hLBpos.le

theorem Rfac_tight_lipschitz_neg (k1 k2 k3 k4 k5 k6 R : ℝ) (hR : 0 ≤ R)
    (ha1 : k1 ≤ 0) (hmono1 : k2 + 4 * k3 * R ^ 2 ≤ 0) (hc1 : 0 < k3)
    (hge2_1 : (-2:ℝ) ≤ k1 * R ^ 2 + k2 * R ^ 4 + k3 * R ^ 6)
    (ha4 : k4 ≤ 0) (hmono4 : k5 + 4 * k6 * R ^ 2 ≤ 0) (hc4 : 0 < k6)
    (hge2_4 : (-2:ℝ) ≤ k4 * R ^ 2 + k5 * R ^ 4 + k6 * R ^ 6)
    (hsafe : MtightNeg k4 k5 k6 R < 1) (a b : ℂ) (haR : ‖a‖ ≤ R) (hbR : ‖b‖ ≤ R) :
    |Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a - Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b|
      ≤ RfacLTightNeg k1 k2 k3 k4 k5 k6 R * ‖a - b‖ := by
  have hmono1' : k2 + 3 * k3 * R ^ 2 ≤ 0 := by nlinarith [hc1, sq_nonneg R]
  have hmono4' : k5 + 3 * k6 * R ^ 2 ≤ 0 := by nlinarith [hc4, sq_nonneg R]
  have hDa : 0 < Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a := by
    have : Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a = 1 + radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) a := rfl
    rw [this]; exact Dden_tight_pos k4 k5 k6 R hR ha4 hmono4' hc4 hsafe a haR
  have hDb : 0 < Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b := by
    have : Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b = 1 + radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) b := rfl
    rw [this]; exact Dden_tight_pos k4 k5 k6 R hR ha4 hmono4' hc4 hsafe b hbR
  have hDage : denomLBTightNeg k4 k5 k6 R ≤ Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a := by
    have heq : Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a = 1 + radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) a := rfl
    rw [heq]; exact Dden_tight_ge k4 k5 k6 R hR ha4 hmono4' hc4 a haR
  have hDbge : denomLBTightNeg k4 k5 k6 R ≤ Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b := by
    have heq : Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b = 1 + radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) b := rfl
    rw [heq]; exact Dden_tight_ge k4 k5 k6 R hR ha4 hmono4' hc4 b hbR
  have hLBpos : 0 < denomLBTightNeg k4 k5 k6 R := by unfold denomLBTightNeg; linarith [hsafe]
  have hNa : |Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a| ≤ 1 := by
    have heqN : Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a = Nnum (RCoeffsOf k1 k2 k3 0 0 0 0 0) a := rfl
    rw [heqN]; exact Nnum_tight_bound_neg k1 k2 k3 R hR ha1 hmono1' hc1 hge2_1 a haR
  have hDaUB : |Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a| ≤ 1 := by
    have heqD : Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a = Dden (RCoeffsOf 0 0 0 k4 k5 k6 0 0) a := rfl
    rw [heqD]; exact Dden_tight_bound_neg k4 k5 k6 R hR ha4 hmono4' hc4 hge2_4 a haR
  have hNDlip : |Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a - Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b|
      ≤ LtightNeg k1 k2 k3 R * ‖a - b‖ := by
    have heqN : Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a - Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b
        = radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a - radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) b := by
      show (1 + radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) a) - (1 + radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) b) = _
      ring
    rw [heqN]
    exact radial_tight_lipschitz_neg k1 k2 k3 R hR ha1 hmono1 hc1 a b haR hbR
  have hDDlip : |Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a - Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b|
      ≤ LtightNeg k4 k5 k6 R * ‖a - b‖ := by
    have heqD : Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a - Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b
        = radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) a - radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) b := by
      show (1 + radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) a) - (1 + radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) b) = _
      ring
    rw [heqD]
    exact radial_tight_lipschitz_neg k4 k5 k6 R hR ha4 hmono4 hc4 a b haR hbR
  have heq : Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a - Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b
      = (Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a
            * (Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b - Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a)
          + Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a
            * (Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a - Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b))
        / (Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a * Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b) := by
    unfold Rfac
    rw [div_sub_div _ _ (ne_of_gt hDa) (ne_of_gt hDb)]
    congr 1; ring
  have hnum_le : |Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a
        * (Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b - Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a)
      + Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a
        * (Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a - Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b)|
      ≤ (LtightNeg k4 k5 k6 R + LtightNeg k1 k2 k3 R) * ‖a - b‖ := by
    calc |Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a
          * (Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b - Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a)
        + Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a
          * (Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a - Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b)|
        ≤ |Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a
            * (Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b - Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a)|
          + |Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a
            * (Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a - Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b)| := by
          have := abs_add_three
            (Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a
              * (Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b - Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a))
            (Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a
              * (Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a - Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b)) 0
          simpa using this
      _ = |Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a|
            * |Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b - Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a|
          + |Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a|
            * |Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a - Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b| := by
          rw [abs_mul, abs_mul]
      _ ≤ 1 * (LtightNeg k4 k5 k6 R * ‖a - b‖) + 1 * (LtightNeg k1 k2 k3 R * ‖a - b‖) := by
          have h1 : |Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b - Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a|
              ≤ LtightNeg k4 k5 k6 R * ‖a - b‖ := by rw [abs_sub_comm]; exact hDDlip
          have hLnn1 : 0 ≤ LtightNeg k4 k5 k6 R := by
            unfold LtightNeg; exact mul_nonneg (mul_nonneg (by norm_num) hR) (abs_nonneg _)
          have hLnn2 : 0 ≤ LtightNeg k1 k2 k3 R := by
            unfold LtightNeg; exact mul_nonneg (mul_nonneg (by norm_num) hR) (abs_nonneg _)
          gcongr
      _ = (LtightNeg k4 k5 k6 R + LtightNeg k1 k2 k3 R) * ‖a - b‖ := by ring
  have hden_ge : (denomLBTightNeg k4 k5 k6 R) ^ 2
      ≤ |Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a * Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b| := by
    rw [abs_mul, abs_of_pos hDa, abs_of_pos hDb, sq]
    exact mul_le_mul hDage hDbge hLBpos.le hDa.le
  rw [heq, abs_div]
  calc |Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a
        * (Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b - Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a)
      + Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a
        * (Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a - Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b)|
      / |Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a * Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b|
      ≤ (LtightNeg k4 k5 k6 R + LtightNeg k1 k2 k3 R) * ‖a - b‖ / (denomLBTightNeg k4 k5 k6 R) ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge |>.trans
        apply div_le_div_of_nonneg_right hnum_le (by positivity)
    _ = RfacLTightNeg k1 k2 k3 k4 k5 k6 R * ‖a - b‖ := by unfold RfacLTightNeg; ring

theorem Rfac_tight_dev_bounded_neg (k1 k2 k3 k4 k5 k6 R : ℝ) (hR : 0 ≤ R)
    (ha1 : k1 ≤ 0) (hmono1 : k2 + 3 * k3 * R ^ 2 ≤ 0) (hc1 : 0 < k3)
    (ha4 : k4 ≤ 0) (hmono4 : k5 + 3 * k6 * R ^ 2 ≤ 0) (hc4 : 0 < k6)
    (hsafe : MtightNeg k4 k5 k6 R < 1) (z : ℂ) (hz : ‖z‖ ≤ R) :
    |Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z - 1| ≤ RfacDevUBTightNeg k1 k2 k3 k4 k5 k6 R := by
  have hDpos : 0 < Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z := by
    have : Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z = 1 + radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) z := rfl
    rw [this]; exact Dden_tight_pos k4 k5 k6 R hR ha4 hmono4 hc4 hsafe z hz
  have hDge : denomLBTightNeg k4 k5 k6 R ≤ Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z := by
    have heq : Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z = 1 + radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) z := rfl
    rw [heq]; exact Dden_tight_ge k4 k5 k6 R hR ha4 hmono4 hc4 z hz
  have hLBpos : 0 < denomLBTightNeg k4 k5 k6 R := by unfold denomLBTightNeg; linarith [hsafe]
  have hNrad := radial_tight_bound_neg k1 k2 k3 R hR ha1 hmono1 hc1 z hz
  have hDrad := radial_tight_bound_neg k4 k5 k6 R hR ha4 hmono4 hc4 z hz
  have heq : Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z - 1
      = (Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z - Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z)
        / Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z := by
    unfold Rfac; rw [div_sub_one (ne_of_gt hDpos)]
  have heq2 : Nnum (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z - Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z
      = radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z - radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) z := by
    show (1 + radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z) - (1 + radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) z) = _
    ring
  have hnum_le : |radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z - radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) z|
      ≤ MtightNeg k1 k2 k3 R + MtightNeg k4 k5 k6 R := by
    have h3 := abs_add_three (radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z)
      (-(radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) z)) 0
    have h4 : |radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z - radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) z|
        ≤ |radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z| + |-(radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) z)| := by
      simpa [sub_eq_add_neg] using h3
    rw [abs_neg] at h4
    linarith [hNrad, hDrad, h4]
  rw [heq, heq2, abs_div, abs_of_pos hDpos]
  calc |radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z - radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) z|
      / Dden (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z
      ≤ |radial (⟨k1, k2, k3, 0, 0⟩ : Coeffs) z - radial (⟨k4, k5, k6, 0, 0⟩ : Coeffs) z|
        / denomLBTightNeg k4 k5 k6 R :=
        div_le_div_of_nonneg_left (abs_nonneg _) hLBpos hDge
    _ ≤ (MtightNeg k1 k2 k3 R + MtightNeg k4 k5 k6 R) / denomLBTightNeg k4 k5 k6 R :=
        div_le_div_of_nonneg_right hnum_le hLBpos.le
    _ = RfacDevUBTightNeg k1 k2 k3 k4 k5 k6 R := rfl

/-─────────────────────────────────────────────────────────────────────────────
  Pert-level bounds, mirroring RationalDistortionBounds.lean's `Pert_bounded`/
  `Pert_lipschitz` exactly (`Pert` itself is UNCONDITIONAL — `Rfac θ z - 1`,
  not a denominator-free simplification — so no bridging lemma is needed
  here, unlike TightBoundsNoDenominator.lean's `Pert_eq_nodenom`).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def MPertTightNeg (k1 k2 k3 k4 k5 k6 p1 p2 R : ℝ) : ℝ :=
  RfacDevUBTightNeg k1 k2 k3 k4 k5 k6 R * R + M (⟨0, 0, 0, p1, p2⟩ : Coeffs) R

noncomputable def LPertTightNeg (k1 k2 k3 k4 k5 k6 p1 p2 R : ℝ) : ℝ :=
  RfacDevUBTightNeg k1 k2 k3 k4 k5 k6 R + RfacLTightNeg k1 k2 k3 k4 k5 k6 R * R
    + L (⟨0, 0, 0, p1, p2⟩ : Coeffs) R

theorem Pert_bounded_tight_neg (k1 k2 k3 k4 k5 k6 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (ha1 : k1 ≤ 0) (hmono1 : k2 + 3 * k3 * R ^ 2 ≤ 0) (hc1 : 0 < k3)
    (ha4 : k4 ≤ 0) (hmono4 : k5 + 3 * k6 * R ^ 2 ≤ 0) (hc4 : 0 < k6)
    (hsafe : MtightNeg k4 k5 k6 R < 1) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖Pert (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z‖ ≤ MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R := by
  have h1 : ‖((Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z - 1 : ℝ)) • z‖
      = |Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z - 1| * ‖z‖ := smul_norm _ _
  have h2 : |Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z - 1| ≤ RfacDevUBTightNeg k1 k2 k3 k4 k5 k6 R := by
    have heqR : Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z = Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) z := by
      rfl
    rw [heqR]
    exact Rfac_tight_dev_bounded_neg k1 k2 k3 k4 k5 k6 R hR ha1 hmono1 hc1 ha4 hmono4 hc4 hsafe z hz
  have h3 : ‖Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z‖ ≤ M (⟨0, 0, 0, p1, p2⟩ : Coeffs) R := by
    have := Tang_bounded (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) R hR z hz
    have heq : tangCoeffs (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) = (⟨0, 0, 0, p1, p2⟩ : Coeffs) := rfl
    rwa [heq] at this
  have h2nn : 0 ≤ RfacDevUBTightNeg k1 k2 k3 k4 k5 k6 R := le_trans (abs_nonneg _) h2
  unfold Pert MPertTightNeg
  calc ‖((Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z - 1 : ℝ)) • z + Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z‖
      ≤ ‖((Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z - 1 : ℝ)) • z‖
        + ‖Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z‖ := norm_add_le _ _
    _ = |Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z - 1| * ‖z‖
        + ‖Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z‖ := by rw [h1]
    _ ≤ RfacDevUBTightNeg k1 k2 k3 k4 k5 k6 R * R + M (⟨0, 0, 0, p1, p2⟩ : Coeffs) R := by gcongr

theorem Pert_lipschitz_tight_neg (k1 k2 k3 k4 k5 k6 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (ha1 : k1 ≤ 0) (hmono1_3 : k2 + 3 * k3 * R ^ 2 ≤ 0) (hmono1_4 : k2 + 4 * k3 * R ^ 2 ≤ 0) (hc1 : 0 < k3)
    (hge2_1 : (-2:ℝ) ≤ k1 * R ^ 2 + k2 * R ^ 4 + k3 * R ^ 6)
    (ha4 : k4 ≤ 0) (hmono4_3 : k5 + 3 * k6 * R ^ 2 ≤ 0) (hmono4_4 : k5 + 4 * k6 * R ^ 2 ≤ 0) (hc4 : 0 < k6)
    (hge2_4 : (-2:ℝ) ≤ k4 * R ^ 2 + k5 * R ^ 4 + k6 * R ^ 6)
    (hsafe : MtightNeg k4 k5 k6 R < 1) (a b : ℂ) (haR : ‖a‖ ≤ R) (hbR : ‖b‖ ≤ R) :
    ‖Pert (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Pert (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b‖
      ≤ LPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R * ‖a - b‖ := by
  have heqRa : Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a = Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) a := by
    rfl
  have heqRb : Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b = Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 0 0) b := by
    rfl
  have hRfacA : |Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - 1| ≤ RfacDevUBTightNeg k1 k2 k3 k4 k5 k6 R := by
    rw [heqRa]; exact Rfac_tight_dev_bounded_neg k1 k2 k3 k4 k5 k6 R hR ha1 hmono1_3 hc1 ha4 hmono4_3 hc4 hsafe a haR
  have hRfacLip : |Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b|
      ≤ RfacLTightNeg k1 k2 k3 k4 k5 k6 R * ‖a - b‖ := by
    rw [heqRa, heqRb]
    exact Rfac_tight_lipschitz_neg k1 k2 k3 k4 k5 k6 R hR ha1 hmono1_4 hc1 hge2_1 ha4 hmono4_4 hc4 hge2_4 hsafe a b haR hbR
  have hTangLip : ‖Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b‖
      ≤ L (⟨0, 0, 0, p1, p2⟩ : Coeffs) R * ‖a - b‖ := by
    have := Tang_lipschitz (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) R hR a b haR hbR
    have heq : tangCoeffs (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) = (⟨0, 0, 0, p1, p2⟩ : Coeffs) := rfl
    rwa [heq] at this
  have heq : Pert (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Pert (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b
      = ((Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - 1 : ℝ)) • (a - b)
        + (Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b : ℝ) • b
        + (Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b) := by
    unfold Pert; module
  rw [heq]
  have hstep1 : ‖((Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - 1 : ℝ)) • (a - b)
        + (Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b : ℝ) • b
        + (Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b)‖
      ≤ ‖((Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - 1 : ℝ)) • (a - b)‖
        + ‖(Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b : ℝ) • b‖
        + ‖Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b‖ := by
    have h1 := norm_add_le (((Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - 1 : ℝ)) • (a - b)
      + (Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b : ℝ) • b)
      (Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b)
    have h2 := norm_add_le (((Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - 1 : ℝ)) • (a - b))
      ((Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b : ℝ) • b)
    linarith
  have hnorms : ‖((Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - 1 : ℝ)) • (a - b)‖
        + ‖(Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b : ℝ) • b‖
        + ‖Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b‖
      = |Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - 1| * ‖a - b‖
        + |Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b| * ‖b‖
        + ‖Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b‖ := by
    rw [smul_norm, smul_norm]
  have hLnn : 0 ≤ RfacLTightNeg k1 k2 k3 k4 k5 k6 R := by
    unfold RfacLTightNeg
    have h1 : 0 ≤ LtightNeg k4 k5 k6 R := by
      unfold LtightNeg; exact mul_nonneg (mul_nonneg (by norm_num) hR) (abs_nonneg _)
    have h2 : 0 ≤ LtightNeg k1 k2 k3 R := by
      unfold LtightNeg; exact mul_nonneg (mul_nonneg (by norm_num) hR) (abs_nonneg _)
    positivity
  have hfinal : |Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - 1| * ‖a - b‖
        + |Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Rfac (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b| * ‖b‖
        + ‖Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Tang (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b‖
      ≤ RfacDevUBTightNeg k1 k2 k3 k4 k5 k6 R * ‖a - b‖
        + (RfacLTightNeg k1 k2 k3 k4 k5 k6 R * ‖a - b‖) * R
        + L (⟨0, 0, 0, p1, p2⟩ : Coeffs) R * ‖a - b‖ := by
    gcongr
  have heq2 : RfacDevUBTightNeg k1 k2 k3 k4 k5 k6 R * ‖a - b‖
      + (RfacLTightNeg k1 k2 k3 k4 k5 k6 R * ‖a - b‖) * R + L (⟨0, 0, 0, p1, p2⟩ : Coeffs) R * ‖a - b‖
      = LPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R * ‖a - b‖ := by unfold LPertTightNeg; ring
  linarith [hstep1, hnorms, hfinal, heq2]

/-─────────────────────────────────────────────────────────────────────────────
  Banach existence/uniqueness and CVmap bridge, mirroring
  Pipeline/TightBoundsNoDenominator.lean's corresponding section exactly
  (and, further back, RationalDistortionInjectivity.lean/
  RationalDistortionBridge.lean), with the "neg"-case Pert bounds substituted.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def inverseStepRTightNeg (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ) (y z : ℂ) : ℂ :=
  y - Pert (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z

theorem inverseStepRTightNeg_maps_disk (k1 k2 k3 k4 k5 k6 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (ha1 : k1 ≤ 0) (hmono1 : k2 + 3 * k3 * R ^ 2 ≤ 0) (hc1 : 0 < k3)
    (ha4 : k4 ≤ 0) (hmono4 : k5 + 3 * k6 * R ^ 2 ≤ 0) (hc4 : 0 < k6)
    (hsafe : MtightNeg k4 k5 k6 R < 1) (y z : ℂ)
    (hy : ‖y‖ + MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R ≤ R) (hz : ‖z‖ ≤ R) :
    ‖inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y z‖ ≤ R := by
  unfold inverseStepRTightNeg
  have hp := Pert_bounded_tight_neg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1 hc1 ha4 hmono4 hc4 hsafe z hz
  calc ‖y - Pert (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z‖
      ≤ ‖y‖ + ‖Pert (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z‖ := norm_sub_le _ _
    _ ≤ ‖y‖ + MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R := by gcongr
    _ ≤ R := hy

theorem inverseStepRTightNeg_lipschitz (k1 k2 k3 k4 k5 k6 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (ha1 : k1 ≤ 0) (hmono1_3 : k2 + 3 * k3 * R ^ 2 ≤ 0) (hmono1_4 : k2 + 4 * k3 * R ^ 2 ≤ 0) (hc1 : 0 < k3)
    (hge2_1 : (-2:ℝ) ≤ k1 * R ^ 2 + k2 * R ^ 4 + k3 * R ^ 6)
    (ha4 : k4 ≤ 0) (hmono4_3 : k5 + 3 * k6 * R ^ 2 ≤ 0) (hmono4_4 : k5 + 4 * k6 * R ^ 2 ≤ 0) (hc4 : 0 < k6)
    (hge2_4 : (-2:ℝ) ≤ k4 * R ^ 2 + k5 * R ^ 4 + k6 * R ^ 6)
    (hsafe : MtightNeg k4 k5 k6 R < 1)
    (y a b : ℂ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y a - inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y b‖
      ≤ LPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R * ‖a - b‖ := by
  unfold inverseStepRTightNeg
  have heq : (y - Pert (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a) - (y - Pert (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b)
      = -(Pert (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) a - Pert (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) b) := by abel
  rw [heq, norm_neg]
  exact Pert_lipschitz_tight_neg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
    ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe a b ha hb

theorem MPertTightNeg_nonneg (k1 k2 k3 k4 k5 k6 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (ha4 : k4 ≤ 0) (hmono4 : k5 + 3 * k6 * R ^ 2 ≤ 0) (hc4 : 0 < k6)
    (hsafe : MtightNeg k4 k5 k6 R < 1)
    (h1nn : 0 ≤ MtightNeg k1 k2 k3 R) :
    0 ≤ MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R := by
  have hLBpos : 0 < denomLBTightNeg k4 k5 k6 R := by unfold denomLBTightNeg; linarith [hsafe]
  have h4nn : 0 ≤ MtightNeg k4 k5 k6 R := abs_nonneg _
  have h1 : 0 ≤ RfacDevUBTightNeg k1 k2 k3 k4 k5 k6 R := by
    unfold RfacDevUBTightNeg; positivity
  have h2 : 0 ≤ M (⟨0, 0, 0, p1, p2⟩ : Coeffs) R := by unfold M; positivity
  unfold MPertTightNeg
  have : 0 ≤ RfacDevUBTightNeg k1 k2 k3 k4 k5 k6 R * R := mul_nonneg h1 hR
  linarith

theorem LPertTightNeg_nonneg (k1 k2 k3 k4 k5 k6 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (ha4 : k4 ≤ 0) (hmono4 : k5 + 3 * k6 * R ^ 2 ≤ 0) (hc4 : 0 < k6)
    (hsafe : MtightNeg k4 k5 k6 R < 1) :
    0 ≤ LPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R := by
  have hLBpos : 0 < denomLBTightNeg k4 k5 k6 R := by unfold denomLBTightNeg; linarith [hsafe]
  have h1 : 0 ≤ RfacDevUBTightNeg k1 k2 k3 k4 k5 k6 R := by
    unfold RfacDevUBTightNeg
    have hnum1 : (0:ℝ) ≤ MtightNeg k1 k2 k3 R := abs_nonneg _
    have hnum2 : (0:ℝ) ≤ MtightNeg k4 k5 k6 R := abs_nonneg _
    exact div_nonneg (by linarith) hLBpos.le
  have hL4 : 0 ≤ LtightNeg k4 k5 k6 R := by
    unfold LtightNeg; exact mul_nonneg (mul_nonneg (by norm_num) hR) (abs_nonneg _)
  have hL1 : 0 ≤ LtightNeg k1 k2 k3 R := by
    unfold LtightNeg; exact mul_nonneg (mul_nonneg (by norm_num) hR) (abs_nonneg _)
  have h2 : 0 ≤ RfacLTightNeg k1 k2 k3 k4 k5 k6 R := by
    unfold RfacLTightNeg
    exact div_nonneg (by linarith [hL4, hL1]) (by positivity)
  have h3 : 0 ≤ L (⟨0, 0, 0, p1, p2⟩ : Coeffs) R := by unfold L; positivity
  unfold LPertTightNeg
  have : 0 ≤ RfacLTightNeg k1 k2 k3 k4 k5 k6 R * R := mul_nonneg h2 hR
  linarith

theorem RDist_exists_unique_preimage_tight_neg
    (k1 k2 k3 k4 k5 k6 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (ha1 : k1 ≤ 0) (hmono1_3 : k2 + 3 * k3 * R ^ 2 ≤ 0) (hmono1_4 : k2 + 4 * k3 * R ^ 2 ≤ 0) (hc1 : 0 < k3)
    (hge2_1 : (-2:ℝ) ≤ k1 * R ^ 2 + k2 * R ^ 4 + k3 * R ^ 6)
    (ha4 : k4 ≤ 0) (hmono4_3 : k5 + 3 * k6 * R ^ 2 ≤ 0) (hmono4_4 : k5 + 4 * k6 * R ^ 2 ≤ 0) (hc4 : 0 < k6)
    (hge2_4 : (-2:ℝ) ≤ k4 * R ^ 2 + k5 * R ^ 4 + k6 * R ^ 6)
    (hsafe : MtightNeg k4 k5 k6 R < 1)
    (hcontract : LPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R < 1)
    (y : ℂ) (hy : ‖y‖ + MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R ≤ R) :
    ∃! z : ℂ, ‖z‖ ≤ R ∧ RDist (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z = y := by
  set θ := RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2 with hθdef
  have hM_nonneg : (0:ℝ) ≤ MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R :=
    MPertTightNeg_nonneg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha4 hmono4_3 hc4 hsafe (abs_nonneg _)
  have hyR : ‖y‖ ≤ R := by linarith
  have hiff : ∀ z : ℂ, inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y z = z ↔ RDist θ z = y := by
    intro z
    rw [RDist_eq_add_Pert θ z]
    unfold inverseStepRTightNeg
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
  have hMapsTo : Set.MapsTo (inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y) s s := fun z hz =>
    inverseStepRTightNeg_maps_disk k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hc1 ha4 hmono4_3 hc4 hsafe y z hy hz
  set K : NNReal := (LPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R).toNNReal with hK_def
  have hK0 : (0:ℝ) ≤ LPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R :=
    LPertTightNeg_nonneg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha4 hmono4_3 hc4 hsafe
  have hKcoe : (K : ℝ) = LPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R := Real.coe_toNNReal _ hK0
  have hKlt1 : K < 1 := by
    rw [← NNReal.coe_lt_coe, hKcoe]; simpa using hcontract
  have hLip : LipschitzWith K (hMapsTo.restrict (inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y) s s) := by
    apply LipschitzWith.of_dist_le_mul
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Set.MapsTo.restrict, Subtype.dist_eq]
    rw [hKcoe]
    have := inverseStepRTightNeg_lipschitz k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
      ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe y a b ha hb
    simpa [dist_eq_norm] using this
  have hContract : ContractingWith K (hMapsTo.restrict (inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y) s s) :=
    ⟨hKlt1, hLip⟩
  have hys : y ∈ s := hyR
  have hedist : edist y (inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y y) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨z, hzs, hfz, _, _⟩ := hContract.exists_fixedPoint' hcomplete hMapsTo hys hedist
  refine ⟨z, ⟨hzs, (hiff z).mp hfz⟩, ?_⟩
  rintro w ⟨hws, hDw⟩
  have hfw : inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y w = w := (hiff w).mpr hDw
  have hzw : (⟨z, hzs⟩ : s) = (⟨w, hws⟩ : s) := by
    apply hContract.fixedPoint_unique' (x := (⟨z, hzs⟩ : s)) (y := (⟨w, hws⟩ : s))
    · show (hMapsTo.restrict (inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y) s s) ⟨z, hzs⟩ = ⟨z, hzs⟩
      exact Subtype.ext hfz
    · show (hMapsTo.restrict (inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y) s s) ⟨w, hws⟩ = ⟨w, hws⟩
      exact Subtype.ext hfw
  exact (congrArg Subtype.val hzw).symm

noncomputable def RDistInvTightNeg (k1 k2 k3 k4 k5 k6 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (ha1 : k1 ≤ 0) (hmono1_3 : k2 + 3 * k3 * R ^ 2 ≤ 0) (hmono1_4 : k2 + 4 * k3 * R ^ 2 ≤ 0) (hc1 : 0 < k3)
    (hge2_1 : (-2:ℝ) ≤ k1 * R ^ 2 + k2 * R ^ 4 + k3 * R ^ 6)
    (ha4 : k4 ≤ 0) (hmono4_3 : k5 + 3 * k6 * R ^ 2 ≤ 0) (hmono4_4 : k5 + 4 * k6 * R ^ 2 ≤ 0) (hc4 : 0 < k6)
    (hge2_4 : (-2:ℝ) ≤ k4 * R ^ 2 + k5 * R ^ 4 + k6 * R ^ 6)
    (hsafe : MtightNeg k4 k5 k6 R < 1)
    (hcontract : LPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R < 1) (y : ℂ) : ℂ :=
  open Classical in
  if h : ‖y‖ + MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R ≤ R then
    (RDist_exists_unique_preimage_tight_neg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
      ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract y h).exists.choose
  else 0

theorem RDist_inverse_invOn_tight_neg (k1 k2 k3 k4 k5 k6 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (ha1 : k1 ≤ 0) (hmono1_3 : k2 + 3 * k3 * R ^ 2 ≤ 0) (hmono1_4 : k2 + 4 * k3 * R ^ 2 ≤ 0) (hc1 : 0 < k3)
    (hge2_1 : (-2:ℝ) ≤ k1 * R ^ 2 + k2 * R ^ 4 + k3 * R ^ 6)
    (ha4 : k4 ≤ 0) (hmono4_3 : k5 + 3 * k6 * R ^ 2 ≤ 0) (hmono4_4 : k5 + 4 * k6 * R ^ 2 ≤ 0) (hc4 : 0 < k6)
    (hge2_4 : (-2:ℝ) ≤ k4 * R ^ 2 + k5 * R ^ 4 + k6 * R ^ 6)
    (hsafe : MtightNeg k4 k5 k6 R < 1)
    (hcontract : LPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R < 1) :
    Set.InvOn
      (RDistInvTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
        ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract)
      (RDist (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2))
      {z : ℂ | ‖z‖ ≤ R ∧ ‖RDist (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z‖
                  + MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R ≤ R}
      {y : ℂ | ‖y‖ + MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R ≤ R} := by
  constructor
  · intro z hz
    obtain ⟨hzR, hyR⟩ := hz
    have huniq := RDist_exists_unique_preimage_tight_neg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1
      hge2_1 ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract
      (RDist (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z) hyR
    have hchoose_spec := huniq.exists.choose_spec
    have hval : RDistInvTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
        ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract (RDist (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z)
        = huniq.exists.choose := by
      show (if h : ‖RDist (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z‖
              + MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R ≤ R then
              (RDist_exists_unique_preimage_tight_neg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
                ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract
                (RDist (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z) h).exists.choose
            else 0) = huniq.exists.choose
      rw [dif_pos hyR]
    rw [hval]
    exact huniq.unique hchoose_spec ⟨hzR, rfl⟩
  · intro y hy
    have hy' : ‖y‖ + MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R ≤ R := hy
    have hval : RDistInvTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
        ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract y
        = (RDist_exists_unique_preimage_tight_neg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
            ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract y hy').exists.choose := by
      show (if h : ‖y‖ + MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R ≤ R then
              (RDist_exists_unique_preimage_tight_neg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
                ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract y h).exists.choose
            else 0) = (RDist_exists_unique_preimage_tight_neg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1
              hge2_1 ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract y hy').exists.choose
      rw [dif_pos hy']
    rw [hval]
    exact (RDist_exists_unique_preimage_tight_neg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
      ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract y hy').exists.choose_spec.2

theorem CVmap_inverse_invOn_tight_neg
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (hden : ∀ x' y' : ℝ, 1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
              + k6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0)
    (R : ℝ) (hR : 0 ≤ R)
    (ha1 : k1 ≤ 0) (hmono1_3 : k2 + 3 * k3 * R ^ 2 ≤ 0) (hmono1_4 : k2 + 4 * k3 * R ^ 2 ≤ 0) (hc1 : 0 < k3)
    (hge2_1 : (-2:ℝ) ≤ k1 * R ^ 2 + k2 * R ^ 4 + k3 * R ^ 6)
    (ha4 : k4 ≤ 0) (hmono4_3 : k5 + 3 * k6 * R ^ 2 ≤ 0) (hmono4_4 : k5 + 4 * k6 * R ^ 2 ≤ 0) (hc4 : 0 < k6)
    (hge2_4 : (-2:ℝ) ≤ k4 * R ^ 2 + k5 * R ^ 4 + k6 * R ^ 6)
    (hsafe : MtightNeg k4 k5 k6 R < 1)
    (hcontract : LPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R < 1) :
    Set.InvOn
      (toComplexEquiv.symm ∘
        RDistInvTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
          ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract
        ∘ toComplexEquiv)
      (CVmap k1 k2 k3 k4 k5 k6 p1 p2 hden)
      (toComplexEquiv.symm ''
        {z : ℂ | ‖z‖ ≤ R ∧ ‖RDist (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) z‖
                    + MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R ≤ R})
      (toComplexEquiv.symm '' {y : ℂ | ‖y‖ + MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R ≤ R}) := by
  set θ := RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2 with hθ
  have hconj : ∀ x : ℂ,
      CVmap k1 k2 k3 k4 k5 k6 p1 p2 hden (toComplexEquiv.symm x) = toComplexEquiv.symm (RDist θ x) := by
    intro x
    have h := CVmap_eq_RDist k1 k2 k3 k4 k5 k6 p1 p2 hden (toComplexEquiv.symm x)
    rw [toComplexEquiv.apply_symm_apply] at h
    have h2 := congrArg toComplexEquiv.symm h
    rwa [Equiv.symm_apply_apply] at h2
  have hmain := conjugate_invOn toComplexEquiv.symm (RDist θ)
    (RDistInvTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
      ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract)
    (CVmap k1 k2 k3 k4 k5 k6 p1 p2 hden)
    {z : ℂ | ‖z‖ ≤ R ∧ ‖RDist θ z‖ + MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R ≤ R}
    {y : ℂ | ‖y‖ + MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R ≤ R}
    hconj (RDist_inverse_invOn_tight_neg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
      ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract)
  simpa [Equiv.symm_symm] using hmain
