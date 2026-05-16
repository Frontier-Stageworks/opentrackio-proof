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
