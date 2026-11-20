/-
  Pipeline/RationalDistortionInjectivity.lean

  Injectivity and existence/uniqueness of a true inverse for RDist on a
  bounded disk, mirroring InverseApproximation.lean's
  D_eq_implies_eq/inverse_step_maps_disk/inverse_step_lipschitz/
  D_exists_unique_preimage architecture, now for the actual rational
  (6-coefficient + tangential) Brown-Conrady model — via RDist's
  "identity + perturbation" form (RDist_eq_add_Pert,
  RationalDistortionBounds.lean) and the contraction condition
  `LPert θ R < 1` in place of `|t|·L θ R < 1`.

  Does not modify InverseApproximation.lean, RationalRadialBounds.lean, or
  RationalDistortionBounds.lean.
-/

import Pipeline.RationalDistortionBounds

/-─────────────────────────────────────────────────────────────────────────────
  inverseStepR — the fixed-point iteration map, mirroring `inverseStep` in
  InverseApproximation.lean (there: `y - t•Φ θ z`; here: `y - Pert θ z`, no
  separate `t` — this model's coefficients already carry full strength).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def inverseStepR (θ : RCoeffs) (y z : ℂ) : ℂ := y - Pert θ z

theorem inverseStepR_maps_disk (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (y z : ℂ)
    (hy : ‖y‖ + MPert θ R ≤ R) (hz : ‖z‖ ≤ R) :
    ‖inverseStepR θ y z‖ ≤ R := by
  unfold inverseStepR
  have hp := Pert_bounded θ R hR hsafe z hz
  calc ‖y - Pert θ z‖ ≤ ‖y‖ + ‖Pert θ z‖ := norm_sub_le _ _
    _ ≤ ‖y‖ + MPert θ R := by gcongr
    _ ≤ R := hy

theorem inverseStepR_lipschitz (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (y a b : ℂ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖inverseStepR θ y a - inverseStepR θ y b‖ ≤ LPert θ R * ‖a - b‖ := by
  unfold inverseStepR
  have heq : (y - Pert θ a) - (y - Pert θ b) = -(Pert θ a - Pert θ b) := by abel
  rw [heq, norm_neg]
  exact Pert_lipschitz θ R hR hsafe a b ha hb

/-─────────────────────────────────────────────────────────────────────────────
  RDist_eq_implies_eq — injectivity of RDist on the disk, given the
  contraction condition LPert θ R < 1. Mirrors D_eq_implies_eq exactly, with
  Pert in place of t•Φ.
─────────────────────────────────────────────────────────────────────────────-/

theorem RDist_eq_implies_eq (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (hcontract : LPert θ R < 1)
    (a b : ℂ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (hD : RDist θ a = RDist θ b) :
    a = b := by
  have hae := RDist_eq_add_Pert θ a
  have hbe := RDist_eq_add_Pert θ b
  have hsum : a + Pert θ a = b + Pert θ b := by rw [← hae, ← hbe, hD]
  have heq : a - b = -(Pert θ a - Pert θ b) := by linear_combination hsum
  have hlip := Pert_lipschitz θ R hR hsafe a b ha hb
  have hle : ‖a - b‖ ≤ LPert θ R * ‖a - b‖ := by
    calc ‖a - b‖ = ‖Pert θ a - Pert θ b‖ := by rw [heq, norm_neg]
      _ ≤ LPert θ R * ‖a - b‖ := hlip
  have hzero : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

theorem RDist_injective_on_disk (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (hcontract : LPert θ R < 1) :
    Set.InjOn (RDist θ) {z : ℂ | ‖z‖ ≤ R} := by
  intro a ha b hb hDab
  exact RDist_eq_implies_eq θ R hR hsafe hcontract a b ha hb hDab

/-─────────────────────────────────────────────────────────────────────────────
  Nonnegativity of MPert/LPert (needed by the Banach step below) — pure
  unfold + positivity given the denominator-safety margin.
─────────────────────────────────────────────────────────────────────────────-/

theorem MPert_nonneg (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R) (hsafe : denomMargin θ R < 1) :
    0 ≤ MPert θ R := by
  have hLBpos : 0 < denomLB θ R := by
    unfold denomMargin at hsafe; unfold denomLB denomMargin; linarith
  have hNUBnn : 0 ≤ Mrad (numCoeffs θ) R := by unfold Mrad; positivity
  have hDUBnn : 0 ≤ Mrad (denCoeffs θ) R := by unfold Mrad; positivity
  have hDevnn : 0 ≤ RfacDevUB θ R := by unfold RfacDevUB; positivity
  have hMnn : 0 ≤ M (tangCoeffs θ) R := by unfold M; positivity
  unfold MPert
  have : 0 ≤ RfacDevUB θ R * R := mul_nonneg hDevnn hR
  linarith

theorem LPert_nonneg (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R) (hsafe : denomMargin θ R < 1) :
    0 ≤ LPert θ R := by
  have hLBpos : 0 < denomLB θ R := by
    unfold denomMargin at hsafe; unfold denomLB denomMargin; linarith
  have hNumMradnn : 0 ≤ Mrad (numCoeffs θ) R := by unfold Mrad; positivity
  have hDenMradnn : 0 ≤ Mrad (denCoeffs θ) R := by unfold Mrad; positivity
  have hNDnn : 0 ≤ Lrad (denCoeffs θ) R := by unfold Lrad; positivity
  have hLNnn : 0 ≤ Lrad (numCoeffs θ) R := by unfold Lrad; positivity
  have hNUBnn : 0 ≤ NnumUB θ R := by unfold NnumUB; linarith
  have hDUBnn : 0 ≤ DdenUB θ R := by unfold DdenUB; linarith
  have hDevnn : 0 ≤ RfacDevUB θ R := by unfold RfacDevUB; positivity
  have hRfacLnn : 0 ≤ RfacL θ R := by unfold RfacL; positivity
  have hLnn : 0 ≤ L (tangCoeffs θ) R := by unfold L; positivity
  unfold LPert
  have : 0 ≤ RfacL θ R * R := mul_nonneg hRfacLnn hR
  linarith

/-─────────────────────────────────────────────────────────────────────────────
  RDist_exists_unique_preimage — the main theorem: local existence and
  uniqueness of the true inverse of RDist on a buffer disk, via Mathlib's
  Banach fixed-point theorem applied to inverseStepR, exactly mirroring
  D_exists_unique_preimage's proof.
─────────────────────────────────────────────────────────────────────────────-/

theorem RDist_exists_unique_preimage
    (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (hcontract : LPert θ R < 1)
    (y : ℂ) (hy : ‖y‖ + MPert θ R ≤ R) :
    ∃! z : ℂ, ‖z‖ ≤ R ∧ RDist θ z = y := by
  have hM_nonneg : (0:ℝ) ≤ MPert θ R := MPert_nonneg θ R hR hsafe
  have hyR : ‖y‖ ≤ R := by linarith
  have hiff : ∀ z : ℂ, inverseStepR θ y z = z ↔ RDist θ z = y := by
    intro z
    rw [RDist_eq_add_Pert θ z]
    unfold inverseStepR
    constructor
    · intro h; linear_combination -h
    · intro h; linear_combination -h
  set s : Set ℂ := {z : ℂ | ‖z‖ ≤ R} with hs_def
  have hclosed : IsClosed s := by
    have hball : s = Metric.closedBall (0 : ℂ) R := by
      ext z; simp [hs_def, Metric.mem_closedBall, dist_eq_norm]
    rw [hball]; exact Metric.isClosed_closedBall
  have hcomplete : IsComplete s := hclosed.isComplete
  have hMapsTo : Set.MapsTo (inverseStepR θ y) s s := fun z hz =>
    inverseStepR_maps_disk θ R hR hsafe y z hy hz
  set K : NNReal := (LPert θ R).toNNReal with hK_def
  have hK0 : (0:ℝ) ≤ LPert θ R := LPert_nonneg θ R hR hsafe
  have hKcoe : (K : ℝ) = LPert θ R := Real.coe_toNNReal _ hK0
  have hKlt1 : K < 1 := by
    rw [← NNReal.coe_lt_coe, hKcoe]; simpa using hcontract
  have hLip : LipschitzWith K (hMapsTo.restrict (inverseStepR θ y) s s) := by
    apply LipschitzWith.of_dist_le_mul
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Set.MapsTo.restrict, Subtype.dist_eq]
    rw [hKcoe]
    have := inverseStepR_lipschitz θ R hR hsafe y a b ha hb
    simpa [dist_eq_norm] using this
  have hContract : ContractingWith K (hMapsTo.restrict (inverseStepR θ y) s s) := ⟨hKlt1, hLip⟩
  have hys : y ∈ s := hyR
  have hedist : edist y (inverseStepR θ y y) ≠ ⊤ := edist_ne_top _ _
  obtain ⟨z, hzs, hfz, _, _⟩ := hContract.exists_fixedPoint' hcomplete hMapsTo hys hedist
  refine ⟨z, ⟨hzs, (hiff z).mp hfz⟩, ?_⟩
  rintro w ⟨hws, hDw⟩
  have hfw : inverseStepR θ y w = w := (hiff w).mpr hDw
  have hzw : (⟨z, hzs⟩ : s) = (⟨w, hws⟩ : s) := by
    apply hContract.fixedPoint_unique' (x := (⟨z, hzs⟩ : s)) (y := (⟨w, hws⟩ : s))
    · show (hMapsTo.restrict (inverseStepR θ y) s s) ⟨z, hzs⟩ = ⟨z, hzs⟩
      exact Subtype.ext hfz
    · show (hMapsTo.restrict (inverseStepR θ y) s s) ⟨w, hws⟩ = ⟨w, hws⟩
      exact Subtype.ext hfw
  exact (congrArg Subtype.val hzw).symm
