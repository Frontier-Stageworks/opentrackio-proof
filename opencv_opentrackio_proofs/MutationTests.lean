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
