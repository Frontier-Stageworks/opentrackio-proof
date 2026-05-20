/-
  AngleOfView.lean — SLICE-OL-12

  Defines the angle-of-view equations from OpenLensIO §2 and §3.1:
    Eq (6):  r_u / F = tan(α/2)      → angleOfView F r_u := 2 * arctan(r_u / F)
    Eq (14): θ = 2 * arctan(w / 2F)  → fovAngleFromWidth F w

  Theorem: angle_of_view_eq
    Real.tan (angleOfView F r_u / 2) = r_u / F
    Proof: unfolds to Real.tan (Real.arctan (r_u / F)) = r_u / F,
    closed by Real.tan_arctan from Mathlib.

  Note: fovAngleFromWidth F w = angleOfView F (w / 2) is trivially true
  and is not stated as a theorem (trivial definitional tautology).
-/

import FovModel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-─────────────────────────────────────────────────────────────────────────────
  angleOfView — Eq (6)

  §2: r_u / F = tan(α/2), equivalently α = 2 * arctan(r_u / F).
  r_u is the undistorted image-plane radius from ΔP; F > 0 is focal length.
  The definition inverts the tan relation: given r_u and F, compute α.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def angleOfView (F r_u : ℝ) : ℝ :=
  2 * Real.arctan (r_u / F)

/-─────────────────────────────────────────────────────────────────────────────
  fovAngleFromWidth — Eq (14)

  §3.1: θ_Ω' = 2 * arctan(w_Ω' / (2F)).
  The FOV angle for a sensor of width w at focal length F.
  Equivalent to angleOfView F (w / 2): the angle subtended by half the width.
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def fovAngleFromWidth (F w : ℝ) : ℝ :=
  2 * Real.arctan (w / (2 * F))

/-─────────────────────────────────────────────────────────────────────────────
  angle_of_view_eq

  §2 Eq (6): the tangent of half the angle of view equals r_u / F.
  Proof: unfold angleOfView → Real.tan (Real.arctan (r_u / F)) = r_u / F
  → closed by Real.tan_arctan.

  Stated for all F : ℝ. Lean 4 division is total (r_u / 0 = 0), so the theorem
  holds vacuously for F = 0 with junk-value semantics. Physical use requires F > 0
  (focal length); callers enforce this via ValidLensSemantics.
─────────────────────────────────────────────────────────────────────────────-/

theorem angle_of_view_eq (F r_u : ℝ) :
    Real.tan (angleOfView F r_u / 2) = r_u / F := by
  simp [angleOfView, Real.tan_arctan]
