/-
  Pipeline/RadialPipeline.lean

  Proves that after radial parameter conversion, the zero-tangential OpenCV
  distortion pipeline agrees with the OpenLensIO undistortion pipeline.
-/

import Pipeline.OpenCVModel
import DistortionConversion
import PixelEquivalence
import DistortionModel

/-─────────────────────────────────────────────────────────────────────────────
  opencv_openlensio_radial_pipeline_eq

  After radial parameter conversion, the zero-tangential OpenCV distortion
  at normalised point ε' equals (1/F) times the zero-tangential OpenLensIO
  undistortion at the corresponding screen point ⟨F·ε'.x, F·ε'.y⟩.

  Equivalently: F · (CV x-output) = OTI x-output at the screen point.

  The proof reduces both sides to R_cv · coord (after simplifying the zero
  tangential terms), then applies radial_distortion_value_equivalence to
  identify R_cv with R_oti at the scaled radius, and closes by ring.

  Note: OTI RadialCoefficients fields follow the alternating naming convention
  (k1,k3,k5 = numerator; k2,k4,k6 = denominator). The caller must supply
  ⟨l1, l2, l3, l4, l5, l6⟩ with l1,l3,l5 as numerator and l2,l4,l6 as denominator.
─────────────────────────────────────────────────────────────────────────────-/

theorem opencv_openlensio_radial_pipeline_eq
    (k1 k2 k3 k4 k5 k6 l1 l2 l3 l4 l5 l6 F : ℝ)
    (ε' : SensorPoint)
    (hF : F ≠ 0) (hF_pos : 0 < F)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hden_cv : 1 + k4 * (sensorRadius ε') ^ 2 + k5 * (sensorRadius ε') ^ 4
                 + k6 * (sensorRadius ε') ^ 6 ≠ 0)
    (hden_oti : denominatorNonzero ⟨l1, l2, l3, l4, l5, l6⟩
                  (sensorRadius ⟨F * ε'.x, F * ε'.y⟩)) :
    F * distortXCV k1 k2 k3 k4 k5 k6 0 0 ε' hden_cv =
    undistortX ⟨l1, l2, l3, l4, l5, l6⟩ TangentialCoefficients.zero
      ⟨F * ε'.x, F * ε'.y⟩ hden_oti := by
  -- Radius scaling: sensorRadius ⟨F·x, F·y⟩ = F · sensorRadius ε'
  have h_rscale : sensorRadius ⟨F * ε'.x, F * ε'.y⟩ = F * sensorRadius ε' := by
    simp only [sensorRadius]
    rw [show (F * ε'.x) ^ 2 + (F * ε'.y) ^ 2 = F ^ 2 * (ε'.x ^ 2 + ε'.y ^ 2) by ring]
    rw [Real.sqrt_mul (sq_nonneg F), Real.sqrt_sq (le_of_lt hF_pos)]
  -- Radial scale equality from the existing theorem (at r = sensorRadius ε')
  have h_rad := (radial_distortion_value_equivalence k1 k2 k3 k4 k5 k6 l1 l3 l5 l2 l4 l6
      F (sensorRadius ε') hF hl1 hl3 hl5 hl2 hl4 hl6 hden_cv).1
  -- OTI side: name the zero-tangential reduction to radialTerm · (F·ε'.x)
  have h_oti_simp : undistortX ⟨l1, l2, l3, l4, l5, l6⟩ TangentialCoefficients.zero
      ⟨F * ε'.x, F * ε'.y⟩ hden_oti =
      radialTerm ⟨l1, l2, l3, l4, l5, l6⟩ (sensorRadius ⟨F * ε'.x, F * ε'.y⟩) hden_oti
      * (F * ε'.x) :=
    tangential_zero_coefficients_identity _ _ _ _ rfl rfl
  rw [h_oti_simp]
  -- Name the radialTerm expansion (struct projections reduce by rfl)
  have h_rterm : radialTerm ⟨l1, l2, l3, l4, l5, l6⟩
      (sensorRadius ⟨F * ε'.x, F * ε'.y⟩) hden_oti =
      (1 + l1 * (F * sensorRadius ε') ^ 2 + l3 * (F * sensorRadius ε') ^ 4
         + l5 * (F * sensorRadius ε') ^ 6) /
      (1 + l2 * (F * sensorRadius ε') ^ 2 + l4 * (F * sensorRadius ε') ^ 4
         + l6 * (F * sensorRadius ε') ^ 6) := by
    simp only [radialTerm, h_rscale]
  rw [h_rterm]
  -- CV side: zero tangential reduces to R_cv · ε'.x
  simp only [distortXCV, mul_zero, zero_mul, add_zero]
  -- h_rad : R_cv = R_oti (the RHS matches exactly); then ring closes F * R * ε' = R * F * ε'
  rw [← h_rad]
  ring
