/-
  Derivation of OpenTrackIO Principal-Point Conversion from First Principles

  Source: "Conversion of OpenCV to OpenTrackIO (OpenLensIO) lens calibration parameters"
  SMPTE RIS, corrected 2025-09-02.

  The paper converts OpenCV principal-point (cx, cy) to OpenTrackIO projection offset
  (ΔPx, ΔPy).  An earlier version of the paper had a bug: it omitted the half-width
  centering term, producing ΔPx = (w/w_shader) * cx instead of the correct
  ΔPx = (w/w_shader) * (cx - w_shader/2).

  The root cause: OpenCV pixel coordinates are upper-left-origin, but OpenTrackIO
  screen coordinates are center-origin.  The centering term is not arbitrary — it is
  the unique value forced by requiring that the two coordinate systems agree on the
  projected position of every scene point.

  Coordinate systems
  ──────────────────
  OpenCV pixel space:
    A scene point with undistorted normalised coordinate x'' maps to pixel u via
      u = fx * x'' + cx
    Origin is at the upper-left corner of the image.
    cx is the x-pixel coordinate of the principal point (upper-left origin).

  OpenTrackIO screen space:
    The same scene point maps to screen coordinate ε'_d via
      ε'_x,d = F * x''
    with projection offset ΔPx shifting the principal point.
    The pixel coordinate is reconstructed from the screen coordinate via
      u = (w_shader / w) * (ε'_x,d + ΔPx) + w_shader / 2
    Origin is at the CENTER of the image (hence the + w_shader/2 term).

  Consistency condition
  ─────────────────────
  For EVERY scene point x'' : ℝ, both systems must assign the same pixel u:

      fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2

  The paper uses a single scalar focal length F for both axes, with the summary:
      F = (w/w_shader) * fx = (h/h_shader) * fy
  This means the OpenCV calibration is exactly representable by one F only when
  (w/w_shader)*fx = (h/h_shader)*fy.  The 2D theorem makes this explicit.

  This file contains five theorems:

    1. principal_point_conversion_necessary   (1D helper)
         Consistency for all x'' forces F and ΔPx to the corrected formula.

    2. principal_point_conversion_iff         (1D, reusable lemma)
         The 1D consistency condition holds for all x'' iff F and ΔPx have the
         corrected values.

    3. principal_point_conversion_2d_iff      (2D, the camera-model theorem)
         The full 2D consistency condition holds for all (x'', y'') iff both axes
         produce the same scalar F and the corrected ΔPx, ΔPy.

    4. single_focal_length_compatibility      (single-F constraint)
         If 2D consistency holds, both axes force the same F — the OpenCV
         calibration is only exactly representable when (w/ws)*fx = (h/hs)*fy.

    5. buggy_principal_point_conversion_inconsistent   (regression guard)
         The earlier buggy formula (missing -w_shader/2) cannot satisfy consistency
         under any nonzero w and w_shader.
-/

import Mathlib.Tactic

/-
  Theorem 1 — Necessity.

  Given only the consistency condition as a hypothesis, F and ΔPx are uniquely
  determined to be the corrected conversion formulas.
-/
theorem principal_point_conversion_necessary
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hconsist : ∀ x'' : ℝ,
        fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2) :
    F   = (w / w_shader) * fx  ∧
    ΔPx = (w / w_shader) * (cx - w_shader / 2) := by
  have h0 := hconsist 0
  have h1 := hconsist 1
  simp only [mul_zero, zero_add, mul_one] at h0 h1
  -- Clear all divisions/inverses so linarith sees plain linear arithmetic.
  field_simp [hw, hw_s] at h0 h1
  -- h0 : cx * w * 2 = w_shader * ΔPx * 2 + w_shader * w        (intercept)
  -- h1 : (fx + cx) * w * 2 = w_shader * (F + ΔPx) * 2 + ...    (slope + intercept)
  -- h1 - h0 isolates F; h0 isolates ΔPx.
  constructor
  · field_simp [hw, hw_s]; nlinarith
  · field_simp [hw, hw_s]; nlinarith

/-
  Theorem 2 — Necessary and sufficient (iff).

  The consistency condition holds for all x'' if and only if F and ΔPx have
  exactly the corrected values.  This is the strongest possible statement:
  the formula characterizes the consistency condition completely.
-/
theorem principal_point_conversion_iff
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0) :
    (∀ x'' : ℝ,
        fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2) ↔
    F   = (w / w_shader) * fx  ∧
    ΔPx = (w / w_shader) * (cx - w_shader / 2) :=
  ⟨principal_point_conversion_necessary w w_shader fx cx F ΔPx hw hw_s,
   fun ⟨hF, hΔPx⟩ x'' => by rw [hF, hΔPx]; field_simp [hw, hw_s]; ring⟩

/-
  Theorem 3 — 2D necessary and sufficient (the camera-model theorem).

  The paper uses a single scalar focal length F for both axes.  The full 2D
  consistency condition holds for all (x'', y'') iff both axes produce the same
  scalar F and the corrected ΔPx and ΔPy values.

  The proof decomposes into two independent 1D problems by specialising:
    x-axis: hconsist x'' 0  (the .1 component, independent of y'')
    y-axis: hconsist 0 y''  (the .2 component, independent of x'')
  then applies the 1D iff lemma to each.
-/
theorem principal_point_conversion_2d_iff
    (w h w_shader h_shader fx fy cx cy F ΔPx ΔPy : ℝ)
    (hw   : w ≠ 0) (hh   : h ≠ 0)
    (hw_s : w_shader ≠ 0) (hh_s : h_shader ≠ 0) :
    (∀ x'' y'' : ℝ,
        fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2 ∧
        fy * y'' + cy = (h_shader / h) * (F * y'' + ΔPy) + h_shader / 2) ↔
    F   = (w / w_shader) * fx  ∧
    ΔPx = (w / w_shader) * (cx - w_shader / 2) ∧
    F   = (h / h_shader) * fy  ∧
    ΔPy = (h / h_shader) * (cy - h_shader / 2) := by
  constructor
  · intro hconsist
    have hx : ∀ x'' : ℝ,
        fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2 :=
      fun x'' => (hconsist x'' 0).1
    have hy : ∀ y'' : ℝ,
        fy * y'' + cy = (h_shader / h) * (F * y'' + ΔPy) + h_shader / 2 :=
      fun y'' => (hconsist 0 y'').2
    obtain ⟨hFx, hΔPx⟩ := (principal_point_conversion_iff w w_shader fx cx F ΔPx hw hw_s).mp hx
    obtain ⟨hFy, hΔPy⟩ := (principal_point_conversion_iff h h_shader fy cy F ΔPy hh hh_s).mp hy
    exact ⟨hFx, hΔPx, hFy, hΔPy⟩
  · intro ⟨hFx, hΔPx, hFy, hΔPy⟩ x'' y''
    exact ⟨(principal_point_conversion_iff w w_shader fx cx F ΔPx hw hw_s).mpr ⟨hFx, hΔPx⟩ x'',
           (principal_point_conversion_iff h h_shader fy cy F ΔPy hh hh_s).mpr ⟨hFy, hΔPy⟩ y''⟩

/-
  Theorem 4 — Single-F compatibility.

  If 2D consistency holds, both axes independently determine F, and those two
  determinations must agree:
      (w / w_shader) * fx = (h / h_shader) * fy

  This is the condition under which an OpenCV calibration (which has separate fx, fy)
  is exactly representable by the single scalar F of the OpenTrackIO model.
  When it fails, no single F can simultaneously satisfy both axes.
-/
theorem single_focal_length_compatibility
    (w h w_shader h_shader fx fy cx cy F ΔPx ΔPy : ℝ)
    (hw   : w ≠ 0) (hh   : h ≠ 0)
    (hw_s : w_shader ≠ 0) (hh_s : h_shader ≠ 0)
    (hconsist : ∀ x'' y'' : ℝ,
        fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2 ∧
        fy * y'' + cy = (h_shader / h) * (F * y'' + ΔPy) + h_shader / 2) :
    (w / w_shader) * fx = (h / h_shader) * fy := by
  obtain ⟨hFx, _, hFy, _⟩ :=
    (principal_point_conversion_2d_iff w h w_shader h_shader fx fy cx cy F ΔPx ΔPy
      hw hh hw_s hh_s).mp hconsist
  linarith

/-
  Theorem 5 — The buggy formula is inconsistent (regression guard).

  If ΔPx = (w/w_shader) * cx (the earlier erroneous formula, missing -w_shader/2),
  and the consistency condition holds for all x'', then w_shader = 0 — contradicting
  the hypothesis that w_shader ≠ 0.

  The old formula is not merely less precise; under nonzero image and sensor width it
  is mathematically incompatible with coordinate-system consistency.
-/
theorem buggy_principal_point_conversion_inconsistent
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hconsist : ∀ x'' : ℝ,
        fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2)
    (hbug : ΔPx = (w / w_shader) * cx) :
    False := by
  obtain ⟨_, hΔPx⟩ :=
    principal_point_conversion_necessary w w_shader fx cx F ΔPx hw hw_s hconsist
  -- hΔPx : ΔPx = (w / w_shader) * (cx - w_shader / 2)
  -- hbug  : ΔPx = (w / w_shader) * cx
  -- Together they force (w / w_shader) * (w_shader / 2) = 0.
  -- Since w / w_shader ≠ 0, this implies w_shader / 2 = 0,
  -- hence w_shader = 0, contradicting hw_s.
  have hscale_ne : w / w_shader ≠ 0 := div_ne_zero hw hw_s
  have hws2 : (w / w_shader) * (w_shader / 2) = 0 := by linarith
  have hws : w_shader = 0 := by
    have := mul_eq_zero.mp hws2
    rcases this with h | h
    · exact absurd h hscale_ne
    · linarith
  exact hw_s hws
