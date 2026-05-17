/-
  MutationTests.lean — Mutation rejection theorems for OpenCV → OpenTrackIO conversion.

  Each theorem here shows that a plausible wrong formula is rejected by the
  existing semantic consistency conditions, confirming that the positive iff
  theorems in PrincipalPointConversion and DistortionConversion are meaningful.

  Pattern used throughout:
    wrong formula + consistency → degenerate condition   (forces-degeneracy layer)
    wrong formula + consistency + ¬ degenerate → False  (contradiction layer, deferred)
-/

import Mathlib.Tactic
import PrincipalPointConversion
import DistortionConversion

/-
  A — Buggy projection offset: ΔPx = (w/w_shader)*cx (missing the centering term).

  Direct contradiction under w ≠ 0, w_shader ≠ 0.
  Delegates to the existing theorem in PrincipalPointConversion.
-/
theorem buggy_projection_offset_missing_center_inconsistent
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : ΔPx = (w / w_shader) * cx) :
    False :=
  buggy_principal_point_conversion_inconsistent w w_shader fx cx F ΔPx hw hw_s hconsist hbug

/-
  B — Wrong projection offset: ΔPx = cx (unscaled, missing w/w_shader and centering).

  Layer 1 (forces degeneracy): consistency + ΔPx = cx forces
      cx = (w / w_shader) * (cx - w_shader / 2)
-/
theorem wrong_projection_offset_unscaled_forces_degenerate_relation
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : ΔPx = cx) :
    cx = (w / w_shader) * (cx - w_shader / 2) := by
  obtain ⟨_, hΔPx⟩ :=
    principal_point_conversion_necessary w w_shader fx cx F ΔPx hw hw_s hconsist
  linarith

/-
  B — Layer 2: contradiction under the negation of the forced equality.
-/
theorem wrong_projection_offset_unscaled_inconsistent
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hnot : cx ≠ (w / w_shader) * (cx - w_shader / 2))
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : ΔPx = cx) :
    False :=
  hnot (wrong_projection_offset_unscaled_forces_degenerate_relation
    w w_shader fx cx F ΔPx hw hw_s hconsist hbug)

/-
  C — Wrong projection offset: ΔPx = cx - w_shader/2 (centering only, missing w/w_shader scale).

  Layer 1 (forces degeneracy): consistency + ΔPx = cx - w_shader/2 forces
      cx - w_shader/2 = (w / w_shader) * (cx - w_shader/2)
  i.e. the principal-point offset must be a fixed point of the w/w_shader scale.
-/
theorem wrong_projection_offset_minus_half_forces_degenerate_relation
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : ΔPx = cx - w_shader / 2) :
    cx - w_shader / 2 = (w / w_shader) * (cx - w_shader / 2) := by
  obtain ⟨_, hΔPx⟩ :=
    principal_point_conversion_necessary w w_shader fx cx F ΔPx hw hw_s hconsist
  linarith

/-
  C — Layer 2: contradiction under the negation of the forced fixed-point equality.
-/
theorem wrong_projection_offset_minus_half_inconsistent
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hnot : cx - w_shader / 2 ≠ (w / w_shader) * (cx - w_shader / 2))
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : ΔPx = cx - w_shader / 2) :
    False :=
  hnot (wrong_projection_offset_minus_half_forces_degenerate_relation
    w w_shader fx cx F ΔPx hw hw_s hconsist hbug)

/-
  D — Wrong focal length: F = fx (identity, missing the w/w_shader scale factor).

  Layer 1 (forces degeneracy): consistency + F = fx + fx ≠ 0 forces w = w_shader.
-/
theorem wrong_focal_length_identity_forces_degeneracy
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hfx  : fx ≠ 0)
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : F = fx) :
    w = w_shader := by
  obtain ⟨hF, _⟩ :=
    principal_point_conversion_necessary w w_shader fx cx F ΔPx hw hw_s hconsist
  rw [hbug] at hF
  -- hF : fx = (w / w_shader) * fx
  have hscale : w / w_shader = 1 :=
    mul_right_cancel₀ hfx (show (w / w_shader) * fx = 1 * fx by linarith)
  linarith [(div_eq_iff hw_s).mp hscale]

/-
  D — Layer 2: contradiction under w ≠ w_shader.
-/
theorem wrong_focal_length_identity_inconsistent
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hfx  : fx ≠ 0)
    (hne  : w ≠ w_shader)
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : F = fx) :
    False :=
  hne (wrong_focal_length_identity_forces_degeneracy
    w w_shader fx cx F ΔPx hw hw_s hfx hconsist hbug)

/-
  E — Wrong focal length: F = (w_shader/w)*fx (inverted scale).

  Over ℝ, this is satisfiable when w = -w_shader (then w/w_shader = -1 = w_shader/w).
  Positivity assumptions exclude that case, giving unconditional contradiction
  under w ≠ w_shader and fx ≠ 0.
-/
theorem wrong_focal_length_inverted_inconsistent
    (w w_shader fx cx F ΔPx : ℝ)
    (hw_pos   : 0 < w)
    (hw_s_pos : 0 < w_shader)
    (hfx  : fx ≠ 0)
    (hne  : w ≠ w_shader)
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : F = (w_shader / w) * fx) :
    False := by
  have hw  : w ≠ 0 := ne_of_gt hw_pos
  have hw_s : w_shader ≠ 0 := ne_of_gt hw_s_pos
  obtain ⟨hF, _⟩ :=
    principal_point_conversion_necessary w w_shader fx cx F ΔPx hw hw_s hconsist
  rw [hbug] at hF
  -- hF : (w_shader / w) * fx = (w / w_shader) * fx
  have hscale : w_shader / w = w / w_shader :=
    mul_right_cancel₀ hfx (show (w_shader / w) * fx = (w / w_shader) * fx by linarith)
  -- Cross-multiply: w_shader * w_shader = w * w
  have hww : w_shader * w_shader = w * w :=
    (div_eq_div_iff hw hw_s).mp hscale
  -- Factor: (w - w_shader) * (w + w_shader) = 0
  have hfactor : (w - w_shader) * (w + w_shader) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · exact hne (by linarith)
  · linarith

/-
  F — Radial wrong-power mutations.

  Each theorem uses whole_radial_polynomial_iff to get the correct coefficient
  formula, then combines it with the wrong formula to force a power degeneracy.
  Layer 1 forces the degeneracy; layer 2 closes to False under its negation.
-/

-- F.1 Numerator: l1 = k1/F^4  (correct: F^2)  forces  F^2 = F^4
theorem wrong_l1_power_F4_forces_power_degeneracy
    (k1 k2 k3 l1 l3 l5 F : ℝ)
    (hF  : F ≠ 0)
    (hk1 : k1 ≠ 0)
    (hpoly : ∀ r : ℝ,
        k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6 =
        l1 * (F * r) ^ 2 + l3 * (F * r) ^ 4 + l5 * (F * r) ^ 6)
    (hwrong : l1 = k1 / F ^ 4) :
    F ^ 2 = F ^ 4 := by
  obtain ⟨hl1, _, _⟩ := (whole_radial_polynomial_iff k1 k2 k3 l1 l3 l5 F hF).mp hpoly
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have hF4 : F ^ 4 ≠ 0 := pow_ne_zero _ hF
  have heq : k1 / F ^ 2 = k1 / F ^ 4 := by linarith
  exact (mul_left_cancel₀ hk1 (div_eq_div_iff hF2 hF4 |>.mp heq)).symm

theorem wrong_l1_power_F4_inconsistent
    (k1 k2 k3 l1 l3 l5 F : ℝ)
    (hF  : F ≠ 0)
    (hk1 : k1 ≠ 0)
    (hpow : F ^ 2 ≠ F ^ 4)
    (hpoly : ∀ r : ℝ,
        k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6 =
        l1 * (F * r) ^ 2 + l3 * (F * r) ^ 4 + l5 * (F * r) ^ 6)
    (hwrong : l1 = k1 / F ^ 4) :
    False :=
  hpow (wrong_l1_power_F4_forces_power_degeneracy k1 k2 k3 l1 l3 l5 F hF hk1 hpoly hwrong)

-- F.2 Numerator: l3 = k2/F^2  (correct: F^4)  forces  F^2 = F^4
theorem wrong_l3_power_F2_forces_power_degeneracy
    (k1 k2 k3 l1 l3 l5 F : ℝ)
    (hF  : F ≠ 0)
    (hk2 : k2 ≠ 0)
    (hpoly : ∀ r : ℝ,
        k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6 =
        l1 * (F * r) ^ 2 + l3 * (F * r) ^ 4 + l5 * (F * r) ^ 6)
    (hwrong : l3 = k2 / F ^ 2) :
    F ^ 2 = F ^ 4 := by
  obtain ⟨_, hl3, _⟩ := (whole_radial_polynomial_iff k1 k2 k3 l1 l3 l5 F hF).mp hpoly
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have hF4 : F ^ 4 ≠ 0 := pow_ne_zero _ hF
  have heq : k2 / F ^ 4 = k2 / F ^ 2 := by linarith
  exact mul_left_cancel₀ hk2 (div_eq_div_iff hF4 hF2 |>.mp heq)

theorem wrong_l3_power_F2_inconsistent
    (k1 k2 k3 l1 l3 l5 F : ℝ)
    (hF  : F ≠ 0)
    (hk2 : k2 ≠ 0)
    (hpow : F ^ 2 ≠ F ^ 4)
    (hpoly : ∀ r : ℝ,
        k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6 =
        l1 * (F * r) ^ 2 + l3 * (F * r) ^ 4 + l5 * (F * r) ^ 6)
    (hwrong : l3 = k2 / F ^ 2) :
    False :=
  hpow (wrong_l3_power_F2_forces_power_degeneracy k1 k2 k3 l1 l3 l5 F hF hk2 hpoly hwrong)

-- F.3 Numerator: l5 = k3/F^4  (correct: F^6)  forces  F^6 = F^4
theorem wrong_l5_power_F4_forces_power_degeneracy
    (k1 k2 k3 l1 l3 l5 F : ℝ)
    (hF  : F ≠ 0)
    (hk3 : k3 ≠ 0)
    (hpoly : ∀ r : ℝ,
        k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6 =
        l1 * (F * r) ^ 2 + l3 * (F * r) ^ 4 + l5 * (F * r) ^ 6)
    (hwrong : l5 = k3 / F ^ 4) :
    F ^ 6 = F ^ 4 := by
  obtain ⟨_, _, hl5⟩ := (whole_radial_polynomial_iff k1 k2 k3 l1 l3 l5 F hF).mp hpoly
  have hF4 : F ^ 4 ≠ 0 := pow_ne_zero _ hF
  have hF6 : F ^ 6 ≠ 0 := pow_ne_zero _ hF
  have heq : k3 / F ^ 6 = k3 / F ^ 4 := by linarith
  exact (mul_left_cancel₀ hk3 (div_eq_div_iff hF6 hF4 |>.mp heq)).symm

theorem wrong_l5_power_F4_inconsistent
    (k1 k2 k3 l1 l3 l5 F : ℝ)
    (hF  : F ≠ 0)
    (hk3 : k3 ≠ 0)
    (hpow : F ^ 6 ≠ F ^ 4)
    (hpoly : ∀ r : ℝ,
        k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6 =
        l1 * (F * r) ^ 2 + l3 * (F * r) ^ 4 + l5 * (F * r) ^ 6)
    (hwrong : l5 = k3 / F ^ 4) :
    False :=
  hpow (wrong_l5_power_F4_forces_power_degeneracy k1 k2 k3 l1 l3 l5 F hF hk3 hpoly hwrong)

-- F.4 Denominator: l2 = k4/F^4  (correct: F^2)  forces  F^2 = F^4
theorem wrong_l2_power_F4_forces_power_degeneracy
    (k4 k5 k6 l2 l4 l6 F : ℝ)
    (hF  : F ≠ 0)
    (hk4 : k4 ≠ 0)
    (hpoly : ∀ r : ℝ,
        k4 * r ^ 2 + k5 * r ^ 4 + k6 * r ^ 6 =
        l2 * (F * r) ^ 2 + l4 * (F * r) ^ 4 + l6 * (F * r) ^ 6)
    (hwrong : l2 = k4 / F ^ 4) :
    F ^ 2 = F ^ 4 := by
  obtain ⟨hl2, _, _⟩ := (whole_radial_polynomial_iff k4 k5 k6 l2 l4 l6 F hF).mp hpoly
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have hF4 : F ^ 4 ≠ 0 := pow_ne_zero _ hF
  have heq : k4 / F ^ 2 = k4 / F ^ 4 := by linarith
  exact (mul_left_cancel₀ hk4 (div_eq_div_iff hF2 hF4 |>.mp heq)).symm

theorem wrong_l2_power_F4_inconsistent
    (k4 k5 k6 l2 l4 l6 F : ℝ)
    (hF  : F ≠ 0)
    (hk4 : k4 ≠ 0)
    (hpow : F ^ 2 ≠ F ^ 4)
    (hpoly : ∀ r : ℝ,
        k4 * r ^ 2 + k5 * r ^ 4 + k6 * r ^ 6 =
        l2 * (F * r) ^ 2 + l4 * (F * r) ^ 4 + l6 * (F * r) ^ 6)
    (hwrong : l2 = k4 / F ^ 4) :
    False :=
  hpow (wrong_l2_power_F4_forces_power_degeneracy k4 k5 k6 l2 l4 l6 F hF hk4 hpoly hwrong)

-- F.5 Denominator: l4 = k5/F^2  (correct: F^4)  forces  F^2 = F^4
theorem wrong_l4_power_F2_forces_power_degeneracy
    (k4 k5 k6 l2 l4 l6 F : ℝ)
    (hF  : F ≠ 0)
    (hk5 : k5 ≠ 0)
    (hpoly : ∀ r : ℝ,
        k4 * r ^ 2 + k5 * r ^ 4 + k6 * r ^ 6 =
        l2 * (F * r) ^ 2 + l4 * (F * r) ^ 4 + l6 * (F * r) ^ 6)
    (hwrong : l4 = k5 / F ^ 2) :
    F ^ 2 = F ^ 4 := by
  obtain ⟨_, hl4, _⟩ := (whole_radial_polynomial_iff k4 k5 k6 l2 l4 l6 F hF).mp hpoly
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have hF4 : F ^ 4 ≠ 0 := pow_ne_zero _ hF
  have heq : k5 / F ^ 4 = k5 / F ^ 2 := by linarith
  exact mul_left_cancel₀ hk5 (div_eq_div_iff hF4 hF2 |>.mp heq)

theorem wrong_l4_power_F2_inconsistent
    (k4 k5 k6 l2 l4 l6 F : ℝ)
    (hF  : F ≠ 0)
    (hk5 : k5 ≠ 0)
    (hpow : F ^ 2 ≠ F ^ 4)
    (hpoly : ∀ r : ℝ,
        k4 * r ^ 2 + k5 * r ^ 4 + k6 * r ^ 6 =
        l2 * (F * r) ^ 2 + l4 * (F * r) ^ 4 + l6 * (F * r) ^ 6)
    (hwrong : l4 = k5 / F ^ 2) :
    False :=
  hpow (wrong_l4_power_F2_forces_power_degeneracy k4 k5 k6 l2 l4 l6 F hF hk5 hpoly hwrong)

-- F.6 Denominator: l6 = k6/F^4  (correct: F^6)  forces  F^6 = F^4
theorem wrong_l6_power_F4_forces_power_degeneracy
    (k4 k5 k6 l2 l4 l6 F : ℝ)
    (hF  : F ≠ 0)
    (hk6 : k6 ≠ 0)
    (hpoly : ∀ r : ℝ,
        k4 * r ^ 2 + k5 * r ^ 4 + k6 * r ^ 6 =
        l2 * (F * r) ^ 2 + l4 * (F * r) ^ 4 + l6 * (F * r) ^ 6)
    (hwrong : l6 = k6 / F ^ 4) :
    F ^ 6 = F ^ 4 := by
  obtain ⟨_, _, hl6⟩ := (whole_radial_polynomial_iff k4 k5 k6 l2 l4 l6 F hF).mp hpoly
  have hF4 : F ^ 4 ≠ 0 := pow_ne_zero _ hF
  have hF6 : F ^ 6 ≠ 0 := pow_ne_zero _ hF
  have heq : k6 / F ^ 6 = k6 / F ^ 4 := by linarith
  exact (mul_left_cancel₀ hk6 (div_eq_div_iff hF6 hF4 |>.mp heq)).symm

theorem wrong_l6_power_F4_inconsistent
    (k4 k5 k6 l2 l4 l6 F : ℝ)
    (hF  : F ≠ 0)
    (hk6 : k6 ≠ 0)
    (hpow : F ^ 6 ≠ F ^ 4)
    (hpoly : ∀ r : ℝ,
        k4 * r ^ 2 + k5 * r ^ 4 + k6 * r ^ 6 =
        l2 * (F * r) ^ 2 + l4 * (F * r) ^ 4 + l6 * (F * r) ^ 6)
    (hwrong : l6 = k6 / F ^ 4) :
    False :=
  hpow (wrong_l6_power_F4_forces_power_degeneracy k4 k5 k6 l2 l4 l6 F hF hk6 hpoly hwrong)

/-
  G — Tangential wrong-power mutations.

  Uses whole_tangential_field_iff (δx only) — the weaker hypothesis that gives
  q1 = p1/F^2 ∧ q2 = p2/F^2.  Wrong power forces a power degeneracy on F.
-/

-- G.1 q1 = p1/F  (correct: F^2)  forces  F^2 = F
theorem wrong_q1_power_F1_forces_power_degeneracy
    (p1 p2 q1 q2 F : ℝ)
    (hF  : F ≠ 0)
    (hp1 : p1 ≠ 0)
    (hpoly : ∀ x' y' : ℝ,
        2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2) =
        2 * q1 * (F * x') * (F * y') +
          q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2))
    (hwrong : q1 = p1 / F) :
    F ^ 2 = F := by
  obtain ⟨hq1, _⟩ := (whole_tangential_field_iff p1 p2 q1 q2 F hF).mp hpoly
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have heq : p1 / F ^ 2 = p1 / F := by linarith
  exact (mul_left_cancel₀ hp1 (div_eq_div_iff hF2 hF |>.mp heq)).symm

theorem wrong_q1_power_F1_inconsistent
    (p1 p2 q1 q2 F : ℝ)
    (hF   : F ≠ 0)
    (hp1  : p1 ≠ 0)
    (hpow : F ^ 2 ≠ F)
    (hpoly : ∀ x' y' : ℝ,
        2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2) =
        2 * q1 * (F * x') * (F * y') +
          q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2))
    (hwrong : q1 = p1 / F) :
    False :=
  hpow (wrong_q1_power_F1_forces_power_degeneracy p1 p2 q1 q2 F hF hp1 hpoly hwrong)

-- G.2 q1 = p1/F^4  (correct: F^2)  forces  F^2 = F^4
theorem wrong_q1_power_F4_forces_power_degeneracy
    (p1 p2 q1 q2 F : ℝ)
    (hF  : F ≠ 0)
    (hp1 : p1 ≠ 0)
    (hpoly : ∀ x' y' : ℝ,
        2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2) =
        2 * q1 * (F * x') * (F * y') +
          q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2))
    (hwrong : q1 = p1 / F ^ 4) :
    F ^ 2 = F ^ 4 := by
  obtain ⟨hq1, _⟩ := (whole_tangential_field_iff p1 p2 q1 q2 F hF).mp hpoly
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have hF4 : F ^ 4 ≠ 0 := pow_ne_zero _ hF
  have heq : p1 / F ^ 2 = p1 / F ^ 4 := by linarith
  exact (mul_left_cancel₀ hp1 (div_eq_div_iff hF2 hF4 |>.mp heq)).symm

theorem wrong_q1_power_F4_inconsistent
    (p1 p2 q1 q2 F : ℝ)
    (hF   : F ≠ 0)
    (hp1  : p1 ≠ 0)
    (hpow : F ^ 2 ≠ F ^ 4)
    (hpoly : ∀ x' y' : ℝ,
        2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2) =
        2 * q1 * (F * x') * (F * y') +
          q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2))
    (hwrong : q1 = p1 / F ^ 4) :
    False :=
  hpow (wrong_q1_power_F4_forces_power_degeneracy p1 p2 q1 q2 F hF hp1 hpoly hwrong)

-- G.3 q2 = p2/F  (correct: F^2)  forces  F^2 = F
theorem wrong_q2_power_F1_forces_power_degeneracy
    (p1 p2 q1 q2 F : ℝ)
    (hF  : F ≠ 0)
    (hp2 : p2 ≠ 0)
    (hpoly : ∀ x' y' : ℝ,
        2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2) =
        2 * q1 * (F * x') * (F * y') +
          q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2))
    (hwrong : q2 = p2 / F) :
    F ^ 2 = F := by
  obtain ⟨_, hq2⟩ := (whole_tangential_field_iff p1 p2 q1 q2 F hF).mp hpoly
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have heq : p2 / F ^ 2 = p2 / F := by linarith
  exact (mul_left_cancel₀ hp2 (div_eq_div_iff hF2 hF |>.mp heq)).symm

theorem wrong_q2_power_F1_inconsistent
    (p1 p2 q1 q2 F : ℝ)
    (hF   : F ≠ 0)
    (hp2  : p2 ≠ 0)
    (hpow : F ^ 2 ≠ F)
    (hpoly : ∀ x' y' : ℝ,
        2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2) =
        2 * q1 * (F * x') * (F * y') +
          q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2))
    (hwrong : q2 = p2 / F) :
    False :=
  hpow (wrong_q2_power_F1_forces_power_degeneracy p1 p2 q1 q2 F hF hp2 hpoly hwrong)

-- G.4 q2 = p2/F^4  (correct: F^2)  forces  F^2 = F^4
theorem wrong_q2_power_F4_forces_power_degeneracy
    (p1 p2 q1 q2 F : ℝ)
    (hF  : F ≠ 0)
    (hp2 : p2 ≠ 0)
    (hpoly : ∀ x' y' : ℝ,
        2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2) =
        2 * q1 * (F * x') * (F * y') +
          q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2))
    (hwrong : q2 = p2 / F ^ 4) :
    F ^ 2 = F ^ 4 := by
  obtain ⟨_, hq2⟩ := (whole_tangential_field_iff p1 p2 q1 q2 F hF).mp hpoly
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have hF4 : F ^ 4 ≠ 0 := pow_ne_zero _ hF
  have heq : p2 / F ^ 2 = p2 / F ^ 4 := by linarith
  exact (mul_left_cancel₀ hp2 (div_eq_div_iff hF2 hF4 |>.mp heq)).symm

theorem wrong_q2_power_F4_inconsistent
    (p1 p2 q1 q2 F : ℝ)
    (hF   : F ≠ 0)
    (hp2  : p2 ≠ 0)
    (hpow : F ^ 2 ≠ F ^ 4)
    (hpoly : ∀ x' y' : ℝ,
        2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2) =
        2 * q1 * (F * x') * (F * y') +
          q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2))
    (hwrong : q2 = p2 / F ^ 4) :
    False :=
  hpow (wrong_q2_power_F4_forces_power_degeneracy p1 p2 q1 q2 F hF hp2 hpoly hwrong)
