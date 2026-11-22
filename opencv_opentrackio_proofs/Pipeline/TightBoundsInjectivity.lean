/-
  Pipeline/TightBoundsInjectivity.lean

  An injectivity-ONLY corollary for the trivial-denominator tight case
  (Pipeline/TightBoundsNoDenominator.lean), on the FULL certified disk
  `{z | ‖z‖ ≤ R}` — not the smaller buffer-restricted region
  `CVmap_inverse_invOn_tight` needs for full existence/uniqueness.

  This is the precise distinction audit/REAL_CAMERA_CERTIFICATION_GAPS.md
  needs: `LPert < 1` alone (no `MPert`-buffer condition) suffices for
  INJECTIVITY on the whole disk — the SAME mirror argument
  RationalDistortionInjectivity.lean's `RDist_eq_implies_eq` uses, with
  `Pert_lipschitz_tight_pos` substituted for `Pert_lipschitz` — but genuine
  EXISTENCE of a preimage (an actual two-sided inverse) is only guaranteed on
  the smaller region where the image also lands back in the buffer disk.
  Conflating the two is exactly the overclaim this file prevents by naming
  them separately.

  Reuses, unchanged: `Pert_lipschitz_tight_pos`
  (Pipeline/TightBoundsNoDenominator.lean), `CVmap_eq_RDist`/`toComplexEquiv`
  (Pipeline/RationalDistortionBridge.lean).

  Does not modify any existing file, weaken any existing theorem, or
  introduce axioms.
-/

import Pipeline.TightBoundsNoDenominator

theorem RDist_eq_implies_eq_tight_pos (k1 k2 k3 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (hdisc_h : k2 ^ 2 ≤ 4 * k1 * k3)
    (hdisc_g : (k2 + k3 * R ^ 2) ^ 2 ≤ 4 * (k1 + k2 * R ^ 2 + k3 * R ^ 4) * k3)
    (hdisc_psi : k2 ^ 2 ≤ 3 * k1 * k3) (hc : 0 < k3)
    (hcontract : LPertTightPos k1 k2 k3 p1 p2 R < 1)
    (a b : ℂ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R)
    (hD : RDist (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) a = RDist (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) b) :
    a = b := by
  set θ := RCoeffsOf k1 k2 k3 0 0 0 p1 p2 with hθdef
  have heq : a - b = -(Pert θ a - Pert θ b) := by
    have ha' := RDist_eq_add_Pert θ a
    have hb' := RDist_eq_add_Pert θ b
    have hsum : a + Pert θ a = b + Pert θ b := by rw [← ha', ← hb', hD]
    linear_combination hsum
  have hnormeq : ‖a - b‖ = ‖Pert θ a - Pert θ b‖ := by rw [heq, norm_neg]
  have hlip := Pert_lipschitz_tight_pos k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc a b ha hb
  rw [hθdef] at hnormeq
  have hle : ‖a - b‖ ≤ LPertTightPos k1 k2 k3 p1 p2 R * ‖a - b‖ := by
    calc ‖a - b‖ = ‖Pert (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) a - Pert (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) b‖ := hnormeq
      _ ≤ LPertTightPos k1 k2 k3 p1 p2 R * ‖a - b‖ := hlip
  have hzero : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

theorem RDist_injective_on_disk_tight_pos (k1 k2 k3 p1 p2 R : ℝ) (hR : 0 ≤ R)
    (hdisc_h : k2 ^ 2 ≤ 4 * k1 * k3)
    (hdisc_g : (k2 + k3 * R ^ 2) ^ 2 ≤ 4 * (k1 + k2 * R ^ 2 + k3 * R ^ 4) * k3)
    (hdisc_psi : k2 ^ 2 ≤ 3 * k1 * k3) (hc : 0 < k3)
    (hcontract : LPertTightPos k1 k2 k3 p1 p2 R < 1) :
    Set.InjOn (RDist (RCoeffsOf k1 k2 k3 0 0 0 p1 p2)) {z : ℂ | ‖z‖ ≤ R} := by
  intro a ha b hb hDab
  exact RDist_eq_implies_eq_tight_pos k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc hcontract a b ha hb hDab

theorem CVmap_injective_on_disk_tight_pos (k1 k2 k3 p1 p2 : ℝ)
    (hden : ∀ x' y' : ℝ, 1 + (0:ℝ) * (x' ^ 2 + y' ^ 2) + (0:ℝ) * (x' ^ 2 + y' ^ 2) ^ 2
              + (0:ℝ) * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0)
    (R : ℝ) (hR : 0 ≤ R)
    (hdisc_h : k2 ^ 2 ≤ 4 * k1 * k3)
    (hdisc_g : (k2 + k3 * R ^ 2) ^ 2 ≤ 4 * (k1 + k2 * R ^ 2 + k3 * R ^ 4) * k3)
    (hdisc_psi : k2 ^ 2 ≤ 3 * k1 * k3) (hc : 0 < k3)
    (hcontract : LPertTightPos k1 k2 k3 p1 p2 R < 1) :
    Set.InjOn (CVmap k1 k2 k3 0 0 0 p1 p2 hden) (toComplexEquiv.symm '' {z : ℂ | ‖z‖ ≤ R}) := by
  have hRDistInj := RDist_injective_on_disk_tight_pos k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc hcontract
  intro x hx y hy hCVeq
  obtain ⟨zx, hzx, hzxeq⟩ := hx
  obtain ⟨zy, hzy, hzyeq⟩ := hy
  have hconjx : CVmap k1 k2 k3 0 0 0 p1 p2 hden x = toComplexEquiv.symm (RDist (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) zx) := by
    rw [← hzxeq]
    have h := CVmap_eq_RDist k1 k2 k3 0 0 0 p1 p2 hden (toComplexEquiv.symm zx)
    have h2 := congrArg toComplexEquiv.symm h
    rwa [Equiv.symm_apply_apply] at h2
  have hconjy : CVmap k1 k2 k3 0 0 0 p1 p2 hden y = toComplexEquiv.symm (RDist (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) zy) := by
    rw [← hzyeq]
    have h := CVmap_eq_RDist k1 k2 k3 0 0 0 p1 p2 hden (toComplexEquiv.symm zy)
    have h2 := congrArg toComplexEquiv.symm h
    rwa [Equiv.symm_apply_apply] at h2
  rw [hconjx, hconjy] at hCVeq
  have hReq : RDist (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) zx = RDist (RCoeffsOf k1 k2 k3 0 0 0 p1 p2) zy :=
    toComplexEquiv.symm.injective hCVeq
  have hzxy : zx = zy := hRDistInj hzx hzy hReq
  rw [← hzxeq, ← hzyeq, hzxy]
