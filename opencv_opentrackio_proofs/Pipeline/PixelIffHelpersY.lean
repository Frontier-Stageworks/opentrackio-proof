/-
  Pipeline/PixelIffHelpersY.lean

  Y-axis mirror of Pipeline/PixelIffHelpers.lean. Helper lemmas for the forward
  direction of opencv_openlensio_full_pipeline_pixel_iff_y.
  All lemmas are in the PipelineEquivalence namespace.

  Reuse decision (see docs/laps/y-pixel-equivalence/proof-plan.md): the radial
  ratio fact is re-derived locally rather than reusing PixelIffHelpers.lean's
  `radial_ratio_scaled_eq` with swapped arguments, to avoid a fragile
  `hden`-argument-order dependency across files.
-/

import DistortionConversion

namespace PipelineEquivalence

-- OTI radial ratio at screen point (F*x, F*y) = CV radial ratio at normalised
-- (x, y), multiplied through by y (the y-axis analog of radial_ratio_scaled_eq,
-- which multiplies by x). The radial ratio itself is symmetric in x/y (depends
-- only on x^2+y^2); only which coordinate it is multiplied against differs.
lemma radial_ratio_scaled_eq_y
    (k1 k2 k3 k4 k5 k6 l1 l2 l3 l4 l5 l6 F x y : ℝ)
    (hF : F ≠ 0)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hden : 1 + k4 * (x ^ 2 + y ^ 2) + k5 * (x ^ 2 + y ^ 2) ^ 2
              + k6 * (x ^ 2 + y ^ 2) ^ 3 ≠ 0) :
    (1 + l1 * ((F*x)^2 + (F*y)^2) + l3 * ((F*x)^2 + (F*y)^2)^2
       + l5 * ((F*x)^2 + (F*y)^2)^3) /
    (1 + l2 * ((F*x)^2 + (F*y)^2) + l4 * ((F*x)^2 + (F*y)^2)^2
       + l6 * ((F*x)^2 + (F*y)^2)^3) * (F * y)
    =
    (1 + k1 * (x^2 + y^2) + k2 * (x^2 + y^2)^2 + k3 * (x^2 + y^2)^3) /
    (1 + k4 * (x^2 + y^2) + k5 * (x^2 + y^2)^2 + k6 * (x^2 + y^2)^3) * y
    * F := by
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have hF4 : F ^ 4 ≠ 0 := pow_ne_zero _ hF
  have hF6 : F ^ 6 ≠ 0 := pow_ne_zero _ hF
  have hrsq : (F*x)^2 + (F*y)^2 = F^2 * (x^2 + y^2) := by ring
  rw [hrsq, hl1, hl3, hl5, hl2, hl4, hl6]
  field_simp [hF2, hF4, hF6, hden]

-- OTI tangential (y-shape) at screen point (F*x, F*y) = CV tangential (y-shape)
-- at normalised (x, y). Split into two single-term facts (squared-term half,
-- cross-term half) — not one combined sum — so each is individually rewritable
-- against a left-associative `+` expression, mirroring the x-file's h_tang1/h_tang2
-- split exactly (see proof-run-log.md attempt 2 for why a combined lemma fails).
lemma tangential_scaled_eq_y_sq
    (p1 q1 F x y : ℝ)
    (hF : F ≠ 0)
    (hq1 : q1 = p1 / F ^ 2) :
    q1 * ((F*x)^2 + (F*y)^2 + 2*(F*y)^2) = p1 * (x^2 + y^2 + 2*y^2) := by
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  rw [hq1]; field_simp [hF2]

lemma tangential_scaled_eq_y_cross
    (p2 q2 F x y : ℝ)
    (hF : F ≠ 0)
    (hq2 : q2 = p2 / F ^ 2) :
    2 * q2 * (F*x) * (F*y) = 2 * p2 * x * y := by
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  rw [hq2]; field_simp [hF2]

-- (h_shader/h)*ΔPy + h_shader/2 = cy   (under ΔPy = (h/h_shader)*(cy - h_shader/2))
lemma principal_offset_cancels_y
    (cy h_shader h ΔPy : ℝ)
    (hh : h ≠ 0) (hhs : h_shader ≠ 0)
    (hΔPy : ΔPy = (h / h_shader) * (cy - h_shader / 2)) :
    (h_shader / h) * ΔPy + h_shader / 2 = cy := by
  rw [hΔPy]; field_simp [hh, hhs]; ring

-- If ∀ x y, (fy - h_shader/h) * T_y(x,y) = 0 and p1≠0 ∨ p2≠0, then h_shader/h = fy.
-- Specialization points recomputed directly from the y-shape term (not copied
-- blindly from the x-version's points) — see proof-capsule.md's derivation.
lemma tangential_gap_forces_scale_y
    (p1 p2 fy h_shader h : ℝ)
    (hh : h ≠ 0) (hhs : h_shader ≠ 0)
    (hp : p1 ≠ 0 ∨ p2 ≠ 0)
    (hgap : ∀ x y : ℝ,
        (fy - h_shader / h) * (p1 * (x^2 + y^2 + 2*y^2) + 2 * p2 * x * y) = 0) :
    h_shader / h = fy := by
  rcases hp with hp1 | hp2
  · -- p1 ≠ 0: (1,0) gives (fy - h_shader/h)*p1 = 0 directly
    have h10 := hgap 1 0
    norm_num at h10
    rcases h10 with hc | hp1z
    · linarith
    · exact absurd hp1z hp1
  · -- p2 ≠ 0: (1,1) gives (fy - h_shader/h)*(4*p1+2*p2) = 0
    --          (1,-1) gives (fy - h_shader/h)*(4*p1-2*p2) = 0
    --          subtract → (fy - h_shader/h)*(4*p2) = 0 → h_shader/h = fy
    have h11  := hgap 1 1
    have h1m1 := hgap 1 (-1)
    have : (fy - h_shader / h) * (4 * p2) = 0 := by linarith
    rcases mul_eq_zero.mp this with hc | hp2z
    · linarith
    · have : p2 = 0 := by linarith
      exact absurd this hp2

-- Universal y-pixel equality → (fy - h_shader/h) * y-tangential_term = 0 for all (x', y')
lemma pixel_eq_implies_tangential_gap_y
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fy cy h_shader h F ΔPy : ℝ)
    (hh : h ≠ 0) (hhs : h_shader ≠ 0) (hF : F ≠ 0)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hq1 : q1 = p1 / F ^ 2) (hq2 : q2 = p2 / F ^ 2)
    (hF_eq : F = (h / h_shader) * fy) (hΔPy : ΔPy = (h / h_shader) * (cy - h_shader / 2))
    (hden : ∀ x' y' : ℝ,
        1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
          + k6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0)
    (hpx : ∀ x' y' : ℝ,
      fy * ((1 + k1 * (x' ^ 2 + y' ^ 2) + k2 * (x' ^ 2 + y' ^ 2) ^ 2
               + k3 * (x' ^ 2 + y' ^ 2) ^ 3) /
            (1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
               + k6 * (x' ^ 2 + y' ^ 2) ^ 3) * y'
           + p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) + 2 * p2 * x' * y') + cy
      =
      (h_shader / h) * ((1 + l1 * ((F * x') ^ 2 + (F * y') ^ 2)
                     + l3 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
                     + l5 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3) /
                  (1 + l2 * ((F * x') ^ 2 + (F * y') ^ 2)
                     + l4 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
                     + l6 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3) * (F * y')
                 + q1 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * y') ^ 2)
                 + 2 * q2 * (F * x') * (F * y') + ΔPy)
      + h_shader / 2) :
    ∀ x' y' : ℝ,
      (fy - h_shader / h) * (p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) + 2 * p2 * x' * y') = 0 := by
  intro x' y'
  have hden_xy := hden x' y'
  have hspec    := hpx x' y'
  have h_rad    := radial_ratio_scaled_eq_y k1 k2 k3 k4 k5 k6 l1 l2 l3 l4 l5 l6 F x' y'
                     hF hl1 hl3 hl5 hl2 hl4 hl6 hden_xy
  have hF2      : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have h_tang1  : q1 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * y') ^ 2) =
                  p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) :=
    tangential_scaled_eq_y_sq p1 q1 F x' y' hF hq1
  have h_tang2  : 2 * q2 * (F * x') * (F * y') = 2 * p2 * x' * y' :=
    tangential_scaled_eq_y_cross p2 q2 F x' y' hF hq2
  have h_offset := principal_offset_cancels_y cy h_shader h ΔPy hh hhs hΔPy
  have h_scale  : h_shader / h * F = fy := by rw [hF_eq]; field_simp [hh, hhs]
  rw [h_rad, h_tang1, h_tang2] at hspec
  linear_combination hspec +
    ((1 + k1 * (x' ^ 2 + y' ^ 2) + k2 * (x' ^ 2 + y' ^ 2) ^ 2
        + k3 * (x' ^ 2 + y' ^ 2) ^ 3) /
     (1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
        + k6 * (x' ^ 2 + y' ^ 2) ^ 3) * y') * h_scale +
    h_offset

end PipelineEquivalence
