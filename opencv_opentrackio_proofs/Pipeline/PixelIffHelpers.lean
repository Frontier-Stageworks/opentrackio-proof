/-
  Pipeline/PixelIffHelpers.lean

  Helper lemmas for the forward direction of opencv_openlensio_full_pipeline_pixel_iff.
  All lemmas are in the PipelineEquivalence namespace.
-/

import DistortionConversion

namespace PipelineEquivalence

-- OTI radial ratio at screen point (F*x, F*y) = CV radial ratio at normalised (x, y)
lemma radial_ratio_scaled_eq
    (k1 k2 k3 k4 k5 k6 l1 l2 l3 l4 l5 l6 F x y : ℝ)
    (hF : F ≠ 0)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hden : 1 + k4 * (x ^ 2 + y ^ 2) + k5 * (x ^ 2 + y ^ 2) ^ 2
              + k6 * (x ^ 2 + y ^ 2) ^ 3 ≠ 0) :
    (1 + l1 * ((F*x)^2 + (F*y)^2) + l3 * ((F*x)^2 + (F*y)^2)^2
       + l5 * ((F*x)^2 + (F*y)^2)^3) /
    (1 + l2 * ((F*x)^2 + (F*y)^2) + l4 * ((F*x)^2 + (F*y)^2)^2
       + l6 * ((F*x)^2 + (F*y)^2)^3) * (F * x)
    =
    (1 + k1 * (x^2 + y^2) + k2 * (x^2 + y^2)^2 + k3 * (x^2 + y^2)^3) /
    (1 + k4 * (x^2 + y^2) + k5 * (x^2 + y^2)^2 + k6 * (x^2 + y^2)^3) * x
    * F := by
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have hF4 : F ^ 4 ≠ 0 := pow_ne_zero _ hF
  have hF6 : F ^ 6 ≠ 0 := pow_ne_zero _ hF
  have hrsq : (F*x)^2 + (F*y)^2 = F^2 * (x^2 + y^2) := by ring
  rw [hrsq, hl1, hl3, hl5, hl2, hl4, hl6]
  field_simp [hF2, hF4, hF6, hden]

-- OTI tangential at screen point (F*x, F*y) = CV tangential at normalised (x, y)
lemma tangential_scaled_eq
    (p1 p2 q1 q2 F x y : ℝ)
    (hF : F ≠ 0)
    (hq1 : q1 = p1 / F ^ 2) (hq2 : q2 = p2 / F ^ 2) :
    2 * q1 * (F*x) * (F*y) + q2 * ((F*x)^2 + (F*y)^2 + 2*(F*x)^2)
    = 2 * p1 * x * y + p2 * (x^2 + y^2 + 2*x^2) := by
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  rw [hq1, hq2]; field_simp [hF2]

-- (ws/w)*ΔPx + ws/2 = cx   (under ΔPx = (w/ws)*(cx - ws/2))
lemma principal_offset_cancels
    (cx ws w ΔPx : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0)
    (hΔPx : ΔPx = (w / ws) * (cx - ws / 2)) :
    (ws / w) * ΔPx + ws / 2 = cx := by
  rw [hΔPx]; field_simp [hw, hws]; ring

-- If ∀ x y, (fx - ws/w) * T(x,y) = 0 and p1≠0 ∨ p2≠0, then ws/w = fx
lemma tangential_gap_forces_scale
    (p1 p2 fx ws w : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0)
    (hp : p1 ≠ 0 ∨ p2 ≠ 0)
    (hgap : ∀ x y : ℝ,
        (fx - ws / w) * (2 * p1 * x * y + p2 * (x^2 + y^2 + 2*x^2)) = 0) :
    ws / w = fx := by
  rcases hp with hp1 | hp2
  · -- p1 ≠ 0: (1,1) gives (fx - ws/w)*(2*p1 + 4*p2) = 0
    --          (1,-1) gives (fx - ws/w)*(-2*p1 + 4*p2) = 0
    --          subtract → (fx - ws/w)*(4*p1) = 0 → fx = ws/w
    have h11  := hgap 1 1
    have h1m1 := hgap 1 (-1)
    have : (fx - ws / w) * (4 * p1) = 0 := by linarith
    rcases mul_eq_zero.mp this with hc | hp1z
    · linarith
    · have : p1 = 0 := by linarith
      exact absurd this hp1
  · -- p2 ≠ 0: (0,1) gives (fx - ws/w)*(p2) = 0
    have h01 := hgap 0 1
    simp only [mul_zero, zero_mul, add_zero, zero_add] at h01
    have : (fx - ws / w) * p2 = 0 := by linarith
    rcases mul_eq_zero.mp this with hc | hp2z
    · linarith
    · exact absurd hp2z hp2

-- Universal pixel equality → (fx - ws/w) * tangential_term = 0 for all (x', y')
lemma pixel_eq_implies_tangential_gap
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fx cx ws w F ΔPx : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0) (hF : F ≠ 0)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hq1 : q1 = p1 / F ^ 2) (hq2 : q2 = p2 / F ^ 2)
    (hF_eq : F = (w / ws) * fx) (hΔPx : ΔPx = (w / ws) * (cx - ws / 2))
    (hden : ∀ x' y' : ℝ,
        1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
          + k6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0)
    (h : ∀ x' y' : ℝ,
      fx * ((1 + k1 * (x' ^ 2 + y' ^ 2) + k2 * (x' ^ 2 + y' ^ 2) ^ 2
               + k3 * (x' ^ 2 + y' ^ 2) ^ 3) /
            (1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
               + k6 * (x' ^ 2 + y' ^ 2) ^ 3) * x'
           + 2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2)) + cx
      =
      (ws / w) * ((1 + l1 * ((F * x') ^ 2 + (F * y') ^ 2)
                     + l3 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
                     + l5 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3) /
                  (1 + l2 * ((F * x') ^ 2 + (F * y') ^ 2)
                     + l4 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 2
                     + l6 * ((F * x') ^ 2 + (F * y') ^ 2) ^ 3) * (F * x')
                 + 2 * q1 * (F * x') * (F * y')
                 + q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2) + ΔPx)
      + ws / 2) :
    ∀ x' y' : ℝ,
      (fx - ws / w) * (2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2)) = 0 := by
  intro x' y'
  have hden_xy := hden x' y'
  have hspec    := h x' y'
  have h_rad    := radial_ratio_scaled_eq k1 k2 k3 k4 k5 k6 l1 l2 l3 l4 l5 l6 F x' y'
                     hF hl1 hl3 hl5 hl2 hl4 hl6 hden_xy
  have hF2      : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have h_tang1  : 2 * q1 * (F * x') * (F * y') = 2 * p1 * x' * y' := by
    rw [hq1]; field_simp [hF2]
  have h_tang2  : q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2) =
                  p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2) := by
    rw [hq2]; field_simp [hF2]
  have h_offset := principal_offset_cancels cx ws w ΔPx hw hws hΔPx
  have h_scale  : ws / w * F = fx := by rw [hF_eq]; field_simp [hw, hws]
  rw [h_rad, h_tang1, h_tang2] at hspec
  linear_combination hspec +
    ((1 + k1 * (x' ^ 2 + y' ^ 2) + k2 * (x' ^ 2 + y' ^ 2) ^ 2
        + k3 * (x' ^ 2 + y' ^ 2) ^ 3) /
     (1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
        + k6 * (x' ^ 2 + y' ^ 2) ^ 3) * x') * h_scale +
    h_offset

end PipelineEquivalence
