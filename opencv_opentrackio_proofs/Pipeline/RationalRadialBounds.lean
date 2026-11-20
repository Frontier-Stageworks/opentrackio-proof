/-
  Pipeline/RationalRadialBounds.lean

  Boundedness, Lipschitz, and denominator-safety estimates for the RATIONAL
  radial factor R(r²) = N(r²)/D(r²) of the actual 6-coefficient Brown-Conrady
  model used by distortXCV/distortYCV (OpenCVModel.lean) — as opposed to the
  simplified POLYNOMIAL (denominator-free) model in
  inverse_approximation/InverseApproximation.lean.

  Does NOT modify InverseApproximation.lean's Coeffs/Φ/D/U/M/L or any of its
  theorems. Reuses, by direct import, the two lemmas there that are generic
  enough to apply unchanged: `radial_bounded`/`radial_lipschitz` depend only
  on a `Coeffs` value's `k1,k2,k3` fields (ignoring `p1,p2`), so they bound
  BOTH the new numerator polynomial (via a dummy Coeffs with k1,k2,k3 := our
  k1,k2,k3, p1=p2=0) and the new denominator polynomial (via a dummy Coeffs
  with k1,k2,k3 := our k4,k5,k6, p1=p2=0) without any new proof for those two
  pieces individually.

  ℂ representation throughout, matching InverseApproximation.lean exactly —
  the SensorPoint/CVmap bridge is built separately in
  Pipeline/RationalDistortionBridge.lean via `conjugate_invOn`.
-/

import InverseApproximation

/-─────────────────────────────────────────────────────────────────────────────
  Small, locally-reused triangle-inequality helpers (this Mathlib snapshot has
  no plain two-term `abs_add`; `abs_add_three` with a zero third argument is
  the confirmed working substitute — verified directly before use, not
  guessed).
─────────────────────────────────────────────────────────────────────────────-/

private theorem abs_add_two (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  have h := abs_add_three x y 0
  simpa using h

private theorem abs_sub_le_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  have h := abs_add_two x (-y)
  simpa using h

/-─────────────────────────────────────────────────────────────────────────────
  RCoeffs — the 6 radial + 2 tangential coefficients, OpenCV's OWN sequential
  convention (k1,k2,k3 = numerator; k4,k5,k6 = denominator), matching
  distortXCV/distortYCV exactly — NOT RadialCoefficients' alternating
  convention.
─────────────────────────────────────────────────────────────────────────────-/

structure RCoeffs where
  k1 : ℝ
  k2 : ℝ
  k3 : ℝ
  k4 : ℝ
  k5 : ℝ
  k6 : ℝ
  p1 : ℝ
  p2 : ℝ

/-─────────────────────────────────────────────────────────────────────────────
  numCoeffs, denCoeffs — package the numerator/denominator coefficient
  triples as `Coeffs` values (p1=p2=0) purely so `radial_bounded`/
  `radial_lipschitz` from InverseApproximation.lean apply directly.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def numCoeffs (θ : RCoeffs) : Coeffs := ⟨θ.k1, θ.k2, θ.k3, 0, 0⟩
noncomputable def denCoeffs (θ : RCoeffs) : Coeffs := ⟨θ.k4, θ.k5, θ.k6, 0, 0⟩

/-─────────────────────────────────────────────────────────────────────────────
  Nnum, Dden — the radial numerator/denominator polynomials, INCLUDING their
  own "1 +" baseline (unlike InverseApproximation.lean's bare `radial`, which
  has no baseline — `Nnum`/`Dden` match distortXCV's own
  `1 + k1·r² + k2·r⁴ + k3·r⁶` shape exactly).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def Nnum (θ : RCoeffs) (z : ℂ) : ℝ := 1 + radial (numCoeffs θ) z
noncomputable def Dden (θ : RCoeffs) (z : ℂ) : ℝ := 1 + radial (denCoeffs θ) z

/-─────────────────────────────────────────────────────────────────────────────
  Nnum/Dden bounds and Lipschitz constants, read off `Mrad`/`Lrad` of the
  dummy Coeffs values (the "+1" baseline shifts the bound by exactly 1 and
  cancels exactly in any Lipschitz difference).
─────────────────────────────────────────────────────────────────────────────-/

theorem Nnum_bounded (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    |Nnum θ z - 1| ≤ Mrad (numCoeffs θ) R := by
  have h := radial_bounded (numCoeffs θ) R hR z hz
  unfold Nnum
  have heq : 1 + radial (numCoeffs θ) z - 1 = radial (numCoeffs θ) z := by ring
  rw [heq]; exact h

theorem Dden_bounded (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    |Dden θ z - 1| ≤ Mrad (denCoeffs θ) R := by
  have h := radial_bounded (denCoeffs θ) R hR z hz
  unfold Dden
  have heq : 1 + radial (denCoeffs θ) z - 1 = radial (denCoeffs θ) z := by ring
  rw [heq]; exact h

theorem Nnum_lipschitz (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R) (a b : ℂ)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    |Nnum θ a - Nnum θ b| ≤ Lrad (numCoeffs θ) R * ‖a - b‖ := by
  have h := radial_lipschitz (numCoeffs θ) R hR a b ha hb
  unfold Nnum
  have heq : (1 + radial (numCoeffs θ) a) - (1 + radial (numCoeffs θ) b)
      = radial (numCoeffs θ) a - radial (numCoeffs θ) b := by ring
  rw [heq]; exact h

theorem Dden_lipschitz (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R) (a b : ℂ)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    |Dden θ a - Dden θ b| ≤ Lrad (denCoeffs θ) R * ‖a - b‖ := by
  have h := radial_lipschitz (denCoeffs θ) R hR a b ha hb
  unfold Dden
  have heq : (1 + radial (denCoeffs θ) a) - (1 + radial (denCoeffs θ) b)
      = radial (denCoeffs θ) a - radial (denCoeffs θ) b := by ring
  rw [heq]; exact h

/-─────────────────────────────────────────────────────────────────────────────
  Denominator safety. `denomMargin θ R := Mrad (denCoeffs θ) R =
  |k4|R²+|k5|R⁴+|k6|R⁶`. Whenever this margin is < 1, Dden stays bounded
  below by the explicit, positive quantity `1 - denomMargin θ R` on the
  entire disk ‖z‖ ≤ R.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def denomMargin (θ : RCoeffs) (R : ℝ) : ℝ := Mrad (denCoeffs θ) R

noncomputable def denomLB (θ : RCoeffs) (R : ℝ) : ℝ := 1 - denomMargin θ R

theorem denom_ge (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    denomLB θ R ≤ Dden θ z := by
  have hb := Dden_bounded θ R hR z hz
  have h2 := (abs_le.mp hb).1
  unfold denomLB denomMargin
  linarith

theorem denom_pos (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (z : ℂ) (hz : ‖z‖ ≤ R) :
    0 < Dden θ z := by
  have h := denom_ge θ R hR z hz
  unfold denomLB at h
  linarith

/-─────────────────────────────────────────────────────────────────────────────
  Rfac — the rational radial factor N(r²)/D(r²), i.e. distortXCV/distortYCV's
  own multiplicative radial coefficient, at full strength (no separate "t"
  parameter — this model has none).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def Rfac (θ : RCoeffs) (z : ℂ) : ℝ := Nnum θ z / Dden θ z

noncomputable def NnumUB (θ : RCoeffs) (R : ℝ) : ℝ := 1 + Mrad (numCoeffs θ) R
noncomputable def DdenUB (θ : RCoeffs) (R : ℝ) : ℝ := 1 + Mrad (denCoeffs θ) R

theorem Nnum_abs_le (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    |Nnum θ z| ≤ NnumUB θ R := by
  have h := Nnum_bounded θ R hR z hz
  have h2 := abs_le.mp h
  have hm : 0 ≤ Mrad (numCoeffs θ) R := by unfold Mrad; positivity
  unfold NnumUB
  rw [abs_le]
  constructor <;> linarith [h2.1, h2.2]

theorem Dden_abs_le (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    |Dden θ z| ≤ DdenUB θ R := by
  have h := Dden_bounded θ R hR z hz
  have h2 := abs_le.mp h
  have hm : 0 ≤ Mrad (denCoeffs θ) R := by unfold Mrad; positivity
  unfold DdenUB
  rw [abs_le]
  constructor <;> linarith [h2.1, h2.2]

noncomputable def RfacUB (θ : RCoeffs) (R : ℝ) : ℝ := NnumUB θ R / denomLB θ R

theorem Rfac_bounded (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (z : ℂ) (hz : ‖z‖ ≤ R) :
    |Rfac θ z| ≤ RfacUB θ R := by
  have hDpos := denom_pos θ R hR hsafe z hz
  have hDge := denom_ge θ R hR z hz
  have hNle := Nnum_abs_le θ R hR z hz
  have hLBpos : 0 < denomLB θ R := by
    unfold denomMargin at hsafe
    unfold denomLB denomMargin
    linarith
  unfold Rfac RfacUB
  rw [abs_div, abs_of_pos hDpos]
  calc |Nnum θ z| / Dden θ z ≤ |Nnum θ z| / denomLB θ R :=
        div_le_div_of_nonneg_left (abs_nonneg _) hLBpos hDge
    _ ≤ NnumUB θ R / denomLB θ R :=
        div_le_div_of_nonneg_right hNle hLBpos.le

/-─────────────────────────────────────────────────────────────────────────────
  Rfac_lipschitz — the quotient-rule Lipschitz bound for the rational radial
  factor. This is the genuinely new algebra this file contributes beyond
  InverseApproximation.lean (whose `radial` has no denominator at all):
  |f(a)-f(b)| ≤ (NnumUB·L_D + DdenUB·L_N)/δ² · ‖a-b‖, where δ = denomLB.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def RfacL (θ : RCoeffs) (R : ℝ) : ℝ :=
  (NnumUB θ R * Lrad (denCoeffs θ) R + DdenUB θ R * Lrad (numCoeffs θ) R) / (denomLB θ R) ^ 2

theorem Rfac_lipschitz (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (a b : ℂ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    |Rfac θ a - Rfac θ b| ≤ RfacL θ R * ‖a - b‖ := by
  have hDa := denom_pos θ R hR hsafe a ha
  have hDb := denom_pos θ R hR hsafe b hb
  have hDage := denom_ge θ R hR a ha
  have hDbge := denom_ge θ R hR b hb
  have hLBpos : 0 < denomLB θ R := by
    unfold denomMargin at hsafe
    unfold denomLB denomMargin
    linarith
  have hNa := Nnum_abs_le θ R hR a ha
  have hDaUB := Dden_abs_le θ R hR a ha
  have hNDlip := Nnum_lipschitz θ R hR a b ha hb
  have hDDlip := Dden_lipschitz θ R hR a b ha hb
  have heq : Rfac θ a - Rfac θ b
      = (Nnum θ a * (Dden θ b - Dden θ a) + Dden θ a * (Nnum θ a - Nnum θ b))
        / (Dden θ a * Dden θ b) := by
    unfold Rfac
    rw [div_sub_div _ _ (ne_of_gt hDa) (ne_of_gt hDb)]
    congr 1
    ring
  have hnum_le : |Nnum θ a * (Dden θ b - Dden θ a) + Dden θ a * (Nnum θ a - Nnum θ b)|
      ≤ (NnumUB θ R * Lrad (denCoeffs θ) R + DdenUB θ R * Lrad (numCoeffs θ) R) * ‖a - b‖ := by
    calc |Nnum θ a * (Dden θ b - Dden θ a) + Dden θ a * (Nnum θ a - Nnum θ b)|
        ≤ |Nnum θ a * (Dden θ b - Dden θ a)| + |Dden θ a * (Nnum θ a - Nnum θ b)| := by
          have := abs_add_three (Nnum θ a * (Dden θ b - Dden θ a))
            (Dden θ a * (Nnum θ a - Nnum θ b)) 0
          simpa using this
      _ = |Nnum θ a| * |Dden θ b - Dden θ a| + |Dden θ a| * |Nnum θ a - Nnum θ b| := by
          rw [abs_mul, abs_mul]
      _ ≤ NnumUB θ R * (Lrad (denCoeffs θ) R * ‖a - b‖)
            + DdenUB θ R * (Lrad (numCoeffs θ) R * ‖a - b‖) := by
          have h1 : |Dden θ b - Dden θ a| ≤ Lrad (denCoeffs θ) R * ‖a - b‖ := by
            rw [abs_sub_comm]; exact hDDlip
          have hNnumUBnn : 0 ≤ NnumUB θ R := by
            have : 0 ≤ Mrad (numCoeffs θ) R := by unfold Mrad; positivity
            unfold NnumUB; linarith
          have hDdenUBnn : 0 ≤ DdenUB θ R := by
            have : 0 ≤ Mrad (denCoeffs θ) R := by unfold Mrad; positivity
            unfold DdenUB; linarith
          gcongr
      _ = (NnumUB θ R * Lrad (denCoeffs θ) R + DdenUB θ R * Lrad (numCoeffs θ) R) * ‖a - b‖ := by
          ring
  have hden_ge : (denomLB θ R) ^ 2 ≤ |Dden θ a * Dden θ b| := by
    rw [abs_mul, abs_of_pos hDa, abs_of_pos hDb, sq]
    exact mul_le_mul hDage hDbge hLBpos.le hDa.le
  rw [heq, abs_div]
  calc |Nnum θ a * (Dden θ b - Dden θ a) + Dden θ a * (Nnum θ a - Nnum θ b)|
        / |Dden θ a * Dden θ b|
      ≤ |Nnum θ a * (Dden θ b - Dden θ a) + Dden θ a * (Nnum θ a - Nnum θ b)|
        / (denomLB θ R) ^ 2 :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hden_ge
    _ ≤ ((NnumUB θ R * Lrad (denCoeffs θ) R + DdenUB θ R * Lrad (numCoeffs θ) R) * ‖a - b‖)
        / (denomLB θ R) ^ 2 :=
        div_le_div_of_nonneg_right hnum_le (by positivity)
    _ = RfacL θ R * ‖a - b‖ := by unfold RfacL; ring

/-─────────────────────────────────────────────────────────────────────────────
  RfacDevUB — bound on |Rfac θ z - 1| (the DEVIATION of the rational radial
  factor from its baseline value 1), not just |Rfac θ z| itself. This is what
  gives RDist the "identity + small perturbation" structure
  `RationalDistortionInjectivity.lean` needs (mirroring how
  `D θ t x = x + t•Φ θ x` is identity-plus-perturbation in
  InverseApproximation.lean) — bounding |Rfac| alone (RfacUB) is not enough
  for that purpose, since RfacUB need not be small even when the lens barely
  distorts.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def RfacDevUB (θ : RCoeffs) (R : ℝ) : ℝ :=
  (Mrad (numCoeffs θ) R + Mrad (denCoeffs θ) R) / denomLB θ R

theorem Rfac_dev_bounded (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (z : ℂ) (hz : ‖z‖ ≤ R) :
    |Rfac θ z - 1| ≤ RfacDevUB θ R := by
  have hDpos := denom_pos θ R hR hsafe z hz
  have hLBpos : 0 < denomLB θ R := by
    unfold denomMargin at hsafe
    unfold denomLB denomMargin
    linarith
  have hDge := denom_ge θ R hR z hz
  have hNb := Nnum_bounded θ R hR z hz
  have hDb := Dden_bounded θ R hR z hz
  have heq : Rfac θ z - 1 = (Nnum θ z - Dden θ z) / Dden θ z := by
    unfold Rfac; rw [div_sub_one (ne_of_gt hDpos)]
  have hnum_le : |Nnum θ z - Dden θ z| ≤ Mrad (numCoeffs θ) R + Mrad (denCoeffs θ) R := by
    have heq2 : Nnum θ z - Dden θ z = (Nnum θ z - 1) - (Dden θ z - 1) := by ring
    rw [heq2]
    calc |Nnum θ z - 1 - (Dden θ z - 1)|
        ≤ |Nnum θ z - 1| + |Dden θ z - 1| := abs_sub_le_add _ _
      _ ≤ Mrad (numCoeffs θ) R + Mrad (denCoeffs θ) R := by gcongr
  rw [heq, abs_div, abs_of_pos hDpos]
  calc |Nnum θ z - Dden θ z| / Dden θ z
      ≤ |Nnum θ z - Dden θ z| / denomLB θ R :=
        div_le_div_of_nonneg_left (abs_nonneg _) hLBpos hDge
    _ ≤ (Mrad (numCoeffs θ) R + Mrad (denCoeffs θ) R) / denomLB θ R :=
        div_le_div_of_nonneg_right hnum_le hLBpos.le
    _ = RfacDevUB θ R := rfl
