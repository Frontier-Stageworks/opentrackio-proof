/-
  Pipeline/RationalDistortionBounds.lean

  Combines the rational radial factor (Pipeline/RationalRadialBounds.lean)
  with the tangential displacement into the full forward-distortion map
  `RDist`, matching distortXCV/distortYCV's actual shape exactly:

    RDist θ z = Rfac θ z • z + Tang θ z

  (no separate "+z" identity term and no distortion-strength parameter `t` —
  this model has neither; the rational radial factor already carries its own
  "1 +" baseline). Produces boundedness (`MR`) and Lipschitz (`LR`) constants
  for `RDist` on a disk, combining `RationalRadialBounds.lean`'s `Rfac`
  bounds with InverseApproximation.lean's EXISTING `phi_bounded`/
  `phi_lipschitz` for the tangential part — reused, not reproved: setting a
  dummy `Coeffs`'s k1=k2=k3=0 makes `Φ` reduce to exactly the tangential
  displacement this model needs, so `Tang` below is a direct definitional
  alias of `Φ`, not a new function requiring new bound/Lipschitz proofs.

  Does not modify InverseApproximation.lean or RationalRadialBounds.lean.
-/

import Pipeline.RationalRadialBounds

/-─────────────────────────────────────────────────────────────────────────────
  Tang — the tangential displacement, as a direct alias of Φ at k1=k2=k3=0.
  Confirmed identical in shape to distortXCV/distortYCV's own tangential
  terms: 2p1·z.re·z.im + p2·(r²+2z.re²) (x-component),
  p1·(r²+2z.im²) + 2p2·z.re·z.im (y-component).
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def tangCoeffs (θ : RCoeffs) : Coeffs := ⟨0, 0, 0, θ.p1, θ.p2⟩

noncomputable def Tang (θ : RCoeffs) (z : ℂ) : ℂ := Φ (tangCoeffs θ) z

theorem Tang_bounded (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖Tang θ z‖ ≤ M (tangCoeffs θ) R :=
  phi_bounded (tangCoeffs θ) R hR z hz

theorem Tang_lipschitz (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R) (a b : ℂ)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖Tang θ a - Tang θ b‖ ≤ L (tangCoeffs θ) R * ‖a - b‖ :=
  phi_lipschitz (tangCoeffs θ) R hR a b ha hb

/-─────────────────────────────────────────────────────────────────────────────
  RDist — the full forward-distortion map, matching distortXCV/distortYCV
  packaged as a single complex-valued function.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def RDist (θ : RCoeffs) (z : ℂ) : ℂ := (Rfac θ z : ℝ) • z + Tang θ z

/-─────────────────────────────────────────────────────────────────────────────
  MR, LR — boundedness and Lipschitz constants for RDist on the disk ‖z‖ ≤ R,
  valid whenever the denominator-safety margin (denomMargin θ R < 1) holds.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def MR (θ : RCoeffs) (R : ℝ) : ℝ :=
  RfacUB θ R * R + M (tangCoeffs θ) R

noncomputable def LR (θ : RCoeffs) (R : ℝ) : ℝ :=
  RfacUB θ R + RfacL θ R * R + L (tangCoeffs θ) R

theorem RDist_bounded (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖RDist θ z‖ ≤ MR θ R := by
  have h1 : ‖(Rfac θ z : ℝ) • z‖ = |Rfac θ z| * ‖z‖ := smul_norm _ _
  have h2 : |Rfac θ z| ≤ RfacUB θ R := Rfac_bounded θ R hR hsafe z hz
  have h3 : ‖Tang θ z‖ ≤ M (tangCoeffs θ) R := Tang_bounded θ R hR z hz
  have h2nn : 0 ≤ RfacUB θ R := le_trans (abs_nonneg _) h2
  unfold RDist MR
  calc ‖(Rfac θ z : ℝ) • z + Tang θ z‖
      ≤ ‖(Rfac θ z : ℝ) • z‖ + ‖Tang θ z‖ := norm_add_le _ _
    _ = |Rfac θ z| * ‖z‖ + ‖Tang θ z‖ := by rw [h1]
    _ ≤ RfacUB θ R * R + M (tangCoeffs θ) R := by
        gcongr

theorem RDist_lipschitz (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (a b : ℂ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖RDist θ a - RDist θ b‖ ≤ LR θ R * ‖a - b‖ := by
  have hRfacA : |Rfac θ a| ≤ RfacUB θ R := Rfac_bounded θ R hR hsafe a ha
  have hRfacLip : |Rfac θ a - Rfac θ b| ≤ RfacL θ R * ‖a - b‖ :=
    Rfac_lipschitz θ R hR hsafe a b ha hb
  have hTangLip : ‖Tang θ a - Tang θ b‖ ≤ L (tangCoeffs θ) R * ‖a - b‖ :=
    Tang_lipschitz θ R hR a b ha hb
  have heq : RDist θ a - RDist θ b
      = (Rfac θ a : ℝ) • (a - b) + (Rfac θ a - Rfac θ b : ℝ) • b
        + (Tang θ a - Tang θ b) := by
    unfold RDist
    module
  rw [heq]
  have hstep1 : ‖(Rfac θ a : ℝ) • (a - b) + (Rfac θ a - Rfac θ b : ℝ) • b
        + (Tang θ a - Tang θ b)‖
      ≤ ‖(Rfac θ a : ℝ) • (a - b)‖ + ‖(Rfac θ a - Rfac θ b : ℝ) • b‖
          + ‖Tang θ a - Tang θ b‖ := by
    have h := norm_add_le ((Rfac θ a : ℝ) • (a - b) + (Rfac θ a - Rfac θ b : ℝ) • b)
      (Tang θ a - Tang θ b)
    have h2 := norm_add_le ((Rfac θ a : ℝ) • (a - b)) ((Rfac θ a - Rfac θ b : ℝ) • b)
    linarith
  have hnorms : ‖(Rfac θ a : ℝ) • (a - b)‖ + ‖(Rfac θ a - Rfac θ b : ℝ) • b‖
        + ‖Tang θ a - Tang θ b‖
      = |Rfac θ a| * ‖a - b‖ + |Rfac θ a - Rfac θ b| * ‖b‖ + ‖Tang θ a - Tang θ b‖ := by
    rw [smul_norm, smul_norm]
  have hLBpos : 0 < denomLB θ R := by
    unfold denomMargin at hsafe
    unfold denomLB denomMargin
    linarith
  have hRfacLnn : 0 ≤ RfacL θ R := by
    have hNDnn : 0 ≤ Lrad (denCoeffs θ) R := by unfold Lrad; positivity
    have hLNnn : 0 ≤ Lrad (numCoeffs θ) R := by unfold Lrad; positivity
    have hNUBnn : 0 ≤ NnumUB θ R := by
      have : 0 ≤ Mrad (numCoeffs θ) R := by unfold Mrad; positivity
      unfold NnumUB; linarith
    have hDUBnn : 0 ≤ DdenUB θ R := by
      have : 0 ≤ Mrad (denCoeffs θ) R := by unfold Mrad; positivity
      unfold DdenUB; linarith
    unfold RfacL
    positivity
  have hfinal : |Rfac θ a| * ‖a - b‖ + |Rfac θ a - Rfac θ b| * ‖b‖ + ‖Tang θ a - Tang θ b‖
      ≤ RfacUB θ R * ‖a - b‖ + (RfacL θ R * ‖a - b‖) * R + L (tangCoeffs θ) R * ‖a - b‖ := by
    gcongr
  have heq2 : RfacUB θ R * ‖a - b‖ + (RfacL θ R * ‖a - b‖) * R + L (tangCoeffs θ) R * ‖a - b‖
      = LR θ R * ‖a - b‖ := by unfold LR; ring
  linarith [hstep1, hnorms, hfinal, heq2]

/-─────────────────────────────────────────────────────────────────────────────
  Pert — the perturbation RDist θ z - z, i.e. RDist written in
  "identity + perturbation" form: RDist θ z = z + Pert θ z. This is the form
  needed for the injectivity/existence argument in
  Pipeline/RationalDistortionInjectivity.lean, mirroring
  InverseApproximation.lean's `D θ t x = x + t•Φ θ x` structure — with the
  rational factor's DEVIATION from 1 (`RfacDevUB`, not `RfacUB`) playing the
  role of the "small" part, since `(Rfac θ z)•z = z + (Rfac θ z - 1)•z`.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def Pert (θ : RCoeffs) (z : ℂ) : ℂ :=
  ((Rfac θ z - 1 : ℝ)) • z + Tang θ z

theorem RDist_eq_add_Pert (θ : RCoeffs) (z : ℂ) : RDist θ z = z + Pert θ z := by
  unfold RDist Pert
  module

noncomputable def MPert (θ : RCoeffs) (R : ℝ) : ℝ :=
  RfacDevUB θ R * R + M (tangCoeffs θ) R

noncomputable def LPert (θ : RCoeffs) (R : ℝ) : ℝ :=
  RfacDevUB θ R + RfacL θ R * R + L (tangCoeffs θ) R

theorem Pert_bounded (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖Pert θ z‖ ≤ MPert θ R := by
  have h1 : ‖((Rfac θ z - 1 : ℝ)) • z‖ = |Rfac θ z - 1| * ‖z‖ := smul_norm _ _
  have h2 : |Rfac θ z - 1| ≤ RfacDevUB θ R := Rfac_dev_bounded θ R hR hsafe z hz
  have h3 : ‖Tang θ z‖ ≤ M (tangCoeffs θ) R := Tang_bounded θ R hR z hz
  have h2nn : 0 ≤ RfacDevUB θ R := le_trans (abs_nonneg _) h2
  unfold Pert MPert
  calc ‖((Rfac θ z - 1 : ℝ)) • z + Tang θ z‖
      ≤ ‖((Rfac θ z - 1 : ℝ)) • z‖ + ‖Tang θ z‖ := norm_add_le _ _
    _ = |Rfac θ z - 1| * ‖z‖ + ‖Tang θ z‖ := by rw [h1]
    _ ≤ RfacDevUB θ R * R + M (tangCoeffs θ) R := by gcongr

theorem Pert_lipschitz (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (a b : ℂ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖Pert θ a - Pert θ b‖ ≤ LPert θ R * ‖a - b‖ := by
  have hRfacA : |Rfac θ a - 1| ≤ RfacDevUB θ R := Rfac_dev_bounded θ R hR hsafe a ha
  have hRfacLip : |Rfac θ a - Rfac θ b| ≤ RfacL θ R * ‖a - b‖ :=
    Rfac_lipschitz θ R hR hsafe a b ha hb
  have hTangLip : ‖Tang θ a - Tang θ b‖ ≤ L (tangCoeffs θ) R * ‖a - b‖ :=
    Tang_lipschitz θ R hR a b ha hb
  have heq : Pert θ a - Pert θ b
      = ((Rfac θ a - 1 : ℝ)) • (a - b) + (Rfac θ a - Rfac θ b : ℝ) • b
        + (Tang θ a - Tang θ b) := by
    unfold Pert
    module
  rw [heq]
  have hstep1 : ‖((Rfac θ a - 1 : ℝ)) • (a - b) + (Rfac θ a - Rfac θ b : ℝ) • b
        + (Tang θ a - Tang θ b)‖
      ≤ ‖((Rfac θ a - 1 : ℝ)) • (a - b)‖ + ‖(Rfac θ a - Rfac θ b : ℝ) • b‖
          + ‖Tang θ a - Tang θ b‖ := by
    have h := norm_add_le (((Rfac θ a - 1 : ℝ)) • (a - b) + (Rfac θ a - Rfac θ b : ℝ) • b)
      (Tang θ a - Tang θ b)
    have h2 := norm_add_le (((Rfac θ a - 1 : ℝ)) • (a - b)) ((Rfac θ a - Rfac θ b : ℝ) • b)
    linarith
  have hnorms : ‖((Rfac θ a - 1 : ℝ)) • (a - b)‖ + ‖(Rfac θ a - Rfac θ b : ℝ) • b‖
        + ‖Tang θ a - Tang θ b‖
      = |Rfac θ a - 1| * ‖a - b‖ + |Rfac θ a - Rfac θ b| * ‖b‖ + ‖Tang θ a - Tang θ b‖ := by
    rw [smul_norm, smul_norm]
  have hLBpos : 0 < denomLB θ R := by
    unfold denomMargin at hsafe
    unfold denomLB denomMargin
    linarith
  have hRfacLnn : 0 ≤ RfacL θ R := by
    have hNDnn : 0 ≤ Lrad (denCoeffs θ) R := by unfold Lrad; positivity
    have hLNnn : 0 ≤ Lrad (numCoeffs θ) R := by unfold Lrad; positivity
    have hNUBnn : 0 ≤ NnumUB θ R := by
      have : 0 ≤ Mrad (numCoeffs θ) R := by unfold Mrad; positivity
      unfold NnumUB; linarith
    have hDUBnn : 0 ≤ DdenUB θ R := by
      have : 0 ≤ Mrad (denCoeffs θ) R := by unfold Mrad; positivity
      unfold DdenUB; linarith
    unfold RfacL
    positivity
  have hfinal : |Rfac θ a - 1| * ‖a - b‖ + |Rfac θ a - Rfac θ b| * ‖b‖ + ‖Tang θ a - Tang θ b‖
      ≤ RfacDevUB θ R * ‖a - b‖ + (RfacL θ R * ‖a - b‖) * R + L (tangCoeffs θ) R * ‖a - b‖ := by
    gcongr
  have heq2 : RfacDevUB θ R * ‖a - b‖ + (RfacL θ R * ‖a - b‖) * R + L (tangCoeffs θ) R * ‖a - b‖
      = LPert θ R * ‖a - b‖ := by unfold LPert; ring
  linarith [hstep1, hnorms, hfinal, heq2]
