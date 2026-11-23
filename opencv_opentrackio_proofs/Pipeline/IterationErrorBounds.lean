/-
  Pipeline/IterationErrorBounds.lean

  Extracts an EXPLICIT, quantitative N-iteration error bound for the
  fixed-point iteration `z_{n+1} = inverseStepRTight θ y z_n` (equivalently
  `z_{n+1} = y - Pert θ z_n`, exactly the Picard/Banach iteration used
  throughout this project's Banach fixed-point proofs, and exactly the
  "subtract the distortion displacement, repeat" update rule any real
  undistort-by-iteration implementation would use) — the result the
  existing proofs (`RDist_exists_unique_preimage_tight_pos`/`_neg`,
  Pipeline/TightBoundsNoDenominator.lean / Pipeline/TightBoundsWithDenominator.lean)
  establish EXISTENCE from but do not themselves expose.

  KEY FACT REUSED, NOT REPROVED: Mathlib's
  `ContractingWith.exists_fixedPoint'` already returns, as its own 4th
  (previously discarded, via `_`) component, the quantitative a priori bound

    ∀ n, edist (f^[n] x) y ≤ edist x (f x) * K^n / (1 - K)

  for the SAME contraction `f`, same starting point `x`, same fixed point
  `y`, and same constant `K` the existing Banach proofs already construct.
  Both `RDist_exists_unique_preimage_tight_pos` and
  `RDist_exists_unique_preimage_tight_neg` call
  `hContract.exists_fixedPoint' hcomplete hMapsTo hys hedist` and destructure
  it as `⟨z, hzs, hfz, _, _⟩` — discarding this exact bound. This file
  reconstructs the IDENTICAL contraction (reusing
  `inverseStepRTight_maps_disk`/`inverseStepRTight_lipschitz`/
  `MPertTightPos_nonneg`/`LPertTightPos_nonneg` for the trivial-denominator
  case, and the "_neg" analogues for the rational-denominator case — no new
  Lipschitz/boundedness facts, no new axioms), re-invokes the SAME Mathlib
  lemma, and converts its `edist`/`ENNReal` bound to a `‖·‖`/`ℝ` bound tied
  to `RDistInvTight`/`RDistInvTightNeg` via `ContractingWith.fixedPoint_unique'`
  (the SAME uniqueness lemma the existing proofs already use).

  Starting point convention: `x := y` (start the iteration at the OBSERVED
  distorted point itself — `z_0 = y`, `z_1 = y - Pert θ y`, etc.), matching
  how every concrete numerical undistort-by-iteration routine is written
  (including the exact scheme used for the floating-point cross-checks in
  audit/REAL_CALIBRATION_VALIDATION.md §5).

  Does not modify any existing file, weaken any existing theorem, or
  introduce axioms.
-/

import Pipeline.TightBoundsNoDenominator
import Pipeline.TightBoundsWithDenominator

/-─────────────────────────────────────────────────────────────────────────────
  Pure ENNReal→ℝ conversion helper for the Banach a priori bound's exact
  shape (`ofReal A * K^n / (1-K)`), used identically in both cases below.
─────────────────────────────────────────────────────────────────────────────-/

theorem ennreal_rate_bound_toReal (A B K : ℝ) (hA : 0 ≤ A) (hK0 : 0 ≤ K) (hK1 : K < 1)
    (n : ℕ)
    (h : ENNReal.ofReal B ≤ ENNReal.ofReal A * (K.toNNReal : ENNReal) ^ n / (1 - (K.toNNReal : ENNReal))) :
    B ≤ A * K ^ n / (1 - K) := by
  have hKcoe : (K.toNNReal : ENNReal) = ENNReal.ofReal K := rfl
  rw [hKcoe] at h
  have h1 : (1:ENNReal) - ENNReal.ofReal K = ENNReal.ofReal (1 - K) := by
    rw [ENNReal.ofReal_sub _ hK0, ENNReal.ofReal_one]
  rw [h1, ← ENNReal.ofReal_pow hK0, ← ENNReal.ofReal_mul hA,
    ← ENNReal.ofReal_div_of_pos (by linarith)] at h
  have hnn : (0:ℝ) ≤ A * K ^ n / (1 - K) :=
    div_nonneg (mul_nonneg hA (pow_nonneg hK0 n)) (by linarith)
  exact (ENNReal.ofReal_le_ofReal_iff hnn).mp h

/-─────────────────────────────────────────────────────────────────────────────
  Trivial-denominator (discriminant-positive) case — TUM fr1/fr2.
─────────────────────────────────────────────────────────────────────────────-/

theorem RDist_iteration_error_bound_tight_pos
    (k1 k2 k3 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (hdisc_h : k2 ^ 2 ≤ 4 * k1 * k3)
    (hdisc_g : (k2 + k3 * R ^ 2) ^ 2 ≤ 4 * (k1 + k2 * R ^ 2 + k3 * R ^ 4) * k3)
    (hdisc_psi : k2 ^ 2 ≤ 3 * k1 * k3) (hc : 0 < k3)
    (hcontract : LPertTightPos k1 k2 k3 p1 p2 R < 1)
    (y : ℂ) (hy : ‖y‖ + MPertTightPos k1 k2 k3 p1 p2 R ≤ R) (n : ℕ) :
    ‖(inverseStepRTight k1 k2 k3 p1 p2 y)^[n] y
        - RDistInvTight k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc hcontract y‖
      ≤ MPertTightPos k1 k2 k3 p1 p2 R * (LPertTightPos k1 k2 k3 p1 p2 R) ^ n
          / (1 - LPertTightPos k1 k2 k3 p1 p2 R) := by
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
  have hKlt1 : K < 1 := by rw [← NNReal.coe_lt_coe, hKcoe]; simpa using hcontract
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
  obtain ⟨z, hzs, hfz, _, hrate⟩ := hContract.exists_fixedPoint' hcomplete hMapsTo hys hedist
  -- Identify z with RDistInvTight y, via the SAME `dif_pos`/uniqueness technique
  -- `RDist_inverse_invOn_tight` itself uses.
  have hchoose_spec := (RDist_exists_unique_preimage_tight_pos k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc
    hcontract y hy).exists.choose_spec
  have hval : RDistInvTight k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc hcontract y
      = (RDist_exists_unique_preimage_tight_pos k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc
          hcontract y hy).exists.choose := by
    show (if h : ‖y‖ + MPertTightPos k1 k2 k3 p1 p2 R ≤ R then
            (RDist_exists_unique_preimage_tight_pos k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc
              hcontract y h).exists.choose
          else 0) = _
    rw [dif_pos hy]
  have hwnorm : ‖RDistInvTight k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc hcontract y‖ ≤ R := by
    rw [hval]; exact hchoose_spec.1
  have hwfix : inverseStepRTight k1 k2 k3 p1 p2 y
      (RDistInvTight k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc hcontract y)
      = RDistInvTight k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc hcontract y := by
    apply (hiff _).mpr
    rw [hval]; exact hchoose_spec.2
  have hzeq : z = RDistInvTight k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc hcontract y := by
    have := hContract.fixedPoint_unique'
      (x := (⟨z, hzs⟩ : s))
      (y := (⟨RDistInvTight k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc hcontract y, hwnorm⟩ : s))
      (Subtype.ext hfz) (Subtype.ext hwfix)
    exact congrArg Subtype.val this
  rw [← hzeq]
  -- Bound the "step 0" distance edist y (f y) by MPertTightPos.
  have hstep0 : edist y (inverseStepRTight k1 k2 k3 p1 p2 y y) ≤ ENNReal.ofReal (MPertTightPos k1 k2 k3 p1 p2 R) := by
    rw [edist_dist, dist_eq_norm]
    have heq : y - inverseStepRTight k1 k2 k3 p1 p2 y y = Pert θ y := by
      unfold inverseStepRTight; rw [hθdef]; ring
    rw [heq]
    exact ENNReal.ofReal_le_ofReal (Pert_bounded_tight_pos k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hc y hyR)
  have hrate_n := hrate n
  have hchain : edist ((inverseStepRTight k1 k2 k3 p1 p2 y)^[n] y) z
      ≤ ENNReal.ofReal (MPertTightPos k1 k2 k3 p1 p2 R) * (K:ENNReal) ^ n / (1 - (K:ENNReal)) := by
    calc edist ((inverseStepRTight k1 k2 k3 p1 p2 y)^[n] y) z
        ≤ edist y (inverseStepRTight k1 k2 k3 p1 p2 y y) * (K:ENNReal) ^ n / (1 - (K:ENNReal)) := hrate_n
      _ ≤ ENNReal.ofReal (MPertTightPos k1 k2 k3 p1 p2 R) * (K:ENNReal) ^ n / (1 - (K:ENNReal)) := by
          gcongr
  rw [hK_def] at hchain
  have hgoal_edist : edist ((inverseStepRTight k1 k2 k3 p1 p2 y)^[n] y) z
      = ENNReal.ofReal ‖(inverseStepRTight k1 k2 k3 p1 p2 y)^[n] y - z‖ := by
    rw [edist_dist, dist_eq_norm]
  rw [hgoal_edist] at hchain
  exact ennreal_rate_bound_toReal (MPertTightPos k1 k2 k3 p1 p2 R) _ (LPertTightPos k1 k2 k3 p1 p2 R)
    hM_nonneg hK0 hcontract n hchain

/-─────────────────────────────────────────────────────────────────────────────
  Genuine-rational-denominator case — Azure Kinect DK. Identical structure to
  the "pos" case above, mirroring `RDist_exists_unique_preimage_tight_neg`'s
  own proof exactly, with `Pert_bounded_tight_neg` in place of
  `Pert_bounded_tight_pos`.
─────────────────────────────────────────────────────────────────────────────-/

theorem RDist_iteration_error_bound_tight_neg
    (k1 k2 k3 k4 k5 k6 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (ha1 : k1 ≤ 0) (hmono1_3 : k2 + 3 * k3 * R ^ 2 ≤ 0) (hmono1_4 : k2 + 4 * k3 * R ^ 2 ≤ 0) (hc1 : 0 < k3)
    (hge2_1 : (-2:ℝ) ≤ k1 * R ^ 2 + k2 * R ^ 4 + k3 * R ^ 6)
    (ha4 : k4 ≤ 0) (hmono4_3 : k5 + 3 * k6 * R ^ 2 ≤ 0) (hmono4_4 : k5 + 4 * k6 * R ^ 2 ≤ 0) (hc4 : 0 < k6)
    (hge2_4 : (-2:ℝ) ≤ k4 * R ^ 2 + k5 * R ^ 4 + k6 * R ^ 6)
    (hsafe : MtightNeg k4 k5 k6 R < 1)
    (hcontract : LPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R < 1)
    (y : ℂ) (hy : ‖y‖ + MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R ≤ R) (n : ℕ) :
    ‖(inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y)^[n] y
        - RDistInvTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
            ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract y‖
      ≤ MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R * (LPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R) ^ n
          / (1 - LPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R) := by
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
  have hKlt1 : K < 1 := by rw [← NNReal.coe_lt_coe, hKcoe]; simpa using hcontract
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
  obtain ⟨z, hzs, hfz, _, hrate⟩ := hContract.exists_fixedPoint' hcomplete hMapsTo hys hedist
  have hchoose_spec := (RDist_exists_unique_preimage_tight_neg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4
    hc1 hge2_1 ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract y hy).exists.choose_spec
  have hval : RDistInvTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
      ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract y
      = (RDist_exists_unique_preimage_tight_neg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
          ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract y hy).exists.choose := by
    show (if h : ‖y‖ + MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R ≤ R then
            (RDist_exists_unique_preimage_tight_neg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
              ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract y h).exists.choose
          else 0) = _
    rw [dif_pos hy]
  have hwnorm : ‖RDistInvTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
      ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract y‖ ≤ R := by
    rw [hval]; exact hchoose_spec.1
  have hwfix : inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y
      (RDistInvTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
        ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract y)
      = RDistInvTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
          ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract y := by
    apply (hiff _).mpr
    rw [hval]; exact hchoose_spec.2
  have hzeq : z = RDistInvTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
      ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract y := by
    have := hContract.fixedPoint_unique'
      (x := (⟨z, hzs⟩ : s))
      (y := (⟨RDistInvTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hmono1_4 hc1 hge2_1
          ha4 hmono4_3 hmono4_4 hc4 hge2_4 hsafe hcontract y, hwnorm⟩ : s))
      (Subtype.ext hfz) (Subtype.ext hwfix)
    exact congrArg Subtype.val this
  rw [← hzeq]
  have hstep0 : edist y (inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y y)
      ≤ ENNReal.ofReal (MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R) := by
    rw [edist_dist, dist_eq_norm]
    have heq : y - inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y y = Pert θ y := by
      unfold inverseStepRTightNeg; rw [hθdef]; ring
    rw [heq]
    exact ENNReal.ofReal_le_ofReal
      (Pert_bounded_tight_neg k1 k2 k3 k4 k5 k6 p1 p2 R hR ha1 hmono1_3 hc1 ha4 hmono4_3 hc4 hsafe y hyR)
  have hrate_n := hrate n
  have hchain : edist ((inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y)^[n] y) z
      ≤ ENNReal.ofReal (MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R) * (K:ENNReal) ^ n / (1 - (K:ENNReal)) := by
    calc edist ((inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y)^[n] y) z
        ≤ edist y (inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y y) * (K:ENNReal) ^ n / (1 - (K:ENNReal)) := hrate_n
      _ ≤ ENNReal.ofReal (MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R) * (K:ENNReal) ^ n / (1 - (K:ENNReal)) := by
          gcongr
  rw [hK_def] at hchain
  have hgoal_edist : edist ((inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y)^[n] y) z
      = ENNReal.ofReal ‖(inverseStepRTightNeg k1 k2 k3 k4 k5 k6 p1 p2 y)^[n] y - z‖ := by
    rw [edist_dist, dist_eq_norm]
  rw [hgoal_edist] at hchain
  exact ennreal_rate_bound_toReal (MPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R) _
    (LPertTightNeg k1 k2 k3 k4 k5 k6 p1 p2 R) hM_nonneg hK0 hcontract n hchain
