/-
  MutationTestsY.lean — Y-axis mutation rejection theorems for the tangential
  distortion conversion, required as the discrimination/anti-vacuity check for
  the y-pixel-equivalence LAPS slice (see docs/laps/y-pixel-equivalence/ and
  docs/maps/laps-handoff.md).

  Mirrors the pattern and two representative theorems requested by the MAPS
  handoff from MutationTests.lean's existing q1/q2-power-degeneracy and
  coefficient-swap theorems, restated for the y-tangential term shape
  `p1*(x'^2+y'^2+2*y'^2) + 2*p2*x'*y'` (per whole_tangential_field_2d_iff's δy
  component), not the x-shape.
-/

import Mathlib.Tactic
import DistortionConversion

/-
  Local extraction lemma: the y-shaped tangential polynomial identity implies
  the same q1=p1/F^2, q2=p2/F^2 conversion as the x-shape (whole_tangential_field_iff).
  Proved directly by specialisation, mirroring whole_tangential_field_iff's own
  proof structure with specialisation points recomputed for the y-term shape
  (see docs/laps/y-pixel-equivalence/proof-plan.md for the by-hand derivation
  confirming (1,0) isolates q1 and (1,1) then isolates q2).
-/
theorem whole_tangential_field_iff_y
    (p1 p2 q1 q2 F : ℝ)
    (hF : F ≠ 0) :
    (∀ x' y' : ℝ,
        p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) + 2 * p2 * x' * y' =
        q1 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * y') ^ 2) +
          2 * q2 * (F * x') * (F * y')) ↔
    q1 = p1 / F ^ 2 ∧ q2 = p2 / F ^ 2 := by
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  constructor
  · intro h
    -- (1,0): squared term vanishes for the cross part, isolates q1.
    have h10 := h 1 0
    -- (1,1): uses both q1 and q2.
    have h11 := h 1 1
    simp only [mul_zero, mul_one, add_zero] at h10 h11
    norm_num at h10 h11
    refine ⟨?_, ?_⟩ <;> field_simp <;> nlinarith
  · intro ⟨hq1, hq2⟩ x' y'
    rw [hq1, hq2]
    field_simp

/-
  Y.1 — Wrong F-power: q1 = p1/F^4 (correct: F^2) forces F^2 = F^4.
  Mirrors MutationTests.lean's wrong_q1_power_F4_forces_power_degeneracy, restated
  against the y-shaped tangential polynomial identity.
-/
theorem wrong_q1_power_F4_forces_power_degeneracy_y
    (p1 p2 q1 q2 F : ℝ)
    (hF  : F ≠ 0)
    (hp1 : p1 ≠ 0)
    (hpoly : ∀ x' y' : ℝ,
        p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) + 2 * p2 * x' * y' =
        q1 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * y') ^ 2) +
          2 * q2 * (F * x') * (F * y'))
    (hwrong : q1 = p1 / F ^ 4) :
    F ^ 2 = F ^ 4 := by
  obtain ⟨hq1, _⟩ := (whole_tangential_field_iff_y p1 p2 q1 q2 F hF).mp hpoly
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  have hF4 : F ^ 4 ≠ 0 := pow_ne_zero _ hF
  have heq : p1 / F ^ 2 = p1 / F ^ 4 := by linarith
  exact (mul_left_cancel₀ hp1 (div_eq_div_iff hF2 hF4 |>.mp heq)).symm

theorem wrong_q1_power_F4_inconsistent_y
    (p1 p2 q1 q2 F : ℝ)
    (hF   : F ≠ 0)
    (hp1  : p1 ≠ 0)
    (hpow : F ^ 2 ≠ F ^ 4)
    (hpoly : ∀ x' y' : ℝ,
        p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) + 2 * p2 * x' * y' =
        q1 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * y') ^ 2) +
          2 * q2 * (F * x') * (F * y'))
    (hwrong : q1 = p1 / F ^ 4) :
    False :=
  hpow (wrong_q1_power_F4_forces_power_degeneracy_y p1 p2 q1 q2 F hF hp1 hpoly hwrong)

/-
  Y.2 — Coefficient swap: pairing q1 with p2 instead of p1 (wrong partner) forces
  an almost-always-false arithmetic coincidence p1 = p2, mirroring
  MutationTests.lean's existing q1↔p2-style swap theorems (section H) for the
  y-shaped tangential identity.
-/
theorem wrong_q1_paired_with_p2_forces_coincidence_y
    (p1 p2 q1 q2 F : ℝ)
    (hF  : F ≠ 0)
    (hpoly : ∀ x' y' : ℝ,
        p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) + 2 * p2 * x' * y' =
        q1 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * y') ^ 2) +
          2 * q2 * (F * x') * (F * y'))
    (hwrong : q1 = p2 / F ^ 2) :
    p1 = p2 := by
  obtain ⟨hq1, _⟩ := (whole_tangential_field_iff_y p1 p2 q1 q2 F hF).mp hpoly
  have heq : p1 / F ^ 2 = p2 / F ^ 2 := by rw [← hq1, hwrong]
  field_simp at heq
  exact heq

theorem wrong_q1_paired_with_p2_inconsistent_y
    (p1 p2 q1 q2 F : ℝ)
    (hF    : F ≠ 0)
    (hcoin : p1 ≠ p2)
    (hpoly : ∀ x' y' : ℝ,
        p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) + 2 * p2 * x' * y' =
        q1 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * y') ^ 2) +
          2 * q2 * (F * x') * (F * y'))
    (hwrong : q1 = p2 / F ^ 2) :
    False :=
  hcoin (wrong_q1_paired_with_p2_forces_coincidence_y p1 p2 q1 q2 F hF hpoly hwrong)
