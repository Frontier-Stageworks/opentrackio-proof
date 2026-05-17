/-
  RationalValueWrappers.lean — Slice 1: rational-value-wrappers

  Invariant-carrying rational value types for the OpenTrackIO parser
  verification plan.

  Ref: docs/laps/opentrack-parser-verification/first-slice-contract.md
-/

import Mathlib.Tactic

/-─────────────────────────────────────────────────────────────────────────────
  Structures
─────────────────────────────────────────────────────────────────────────────-/

structure RationalWithPositiveDenominator where
  num     : Int
  den     : Nat
  den_pos : 0 < den

structure NonnegativeRational where
  num     : Nat
  den     : Nat
  den_pos : 0 < den

structure PositiveRational where
  num     : Nat
  den     : Nat
  num_pos : 0 < num
  den_pos : 0 < den

/-─────────────────────────────────────────────────────────────────────────────
  Evaluation functions
─────────────────────────────────────────────────────────────────────────────-/

noncomputable def RationalWithPositiveDenominator.toReal (r : RationalWithPositiveDenominator) : ℝ :=
  (r.num : ℝ) / (r.den : ℝ)

noncomputable def NonnegativeRational.toReal (r : NonnegativeRational) : ℝ :=
  (r.num : ℝ) / (r.den : ℝ)

noncomputable def PositiveRational.toReal (r : PositiveRational) : ℝ :=
  (r.num : ℝ) / (r.den : ℝ)

/-─────────────────────────────────────────────────────────────────────────────
  ℕ-level denominator nonzero
─────────────────────────────────────────────────────────────────────────────-/

theorem rational_with_positive_denominator_den_nat_ne_zero
    (r : RationalWithPositiveDenominator) : r.den ≠ 0 := by
  have h := r.den_pos; omega

theorem nonnegative_rational_den_nat_ne_zero
    (r : NonnegativeRational) : r.den ≠ 0 := by
  have h := r.den_pos; omega

theorem positive_rational_den_nat_ne_zero
    (r : PositiveRational) : r.den ≠ 0 := by
  have h := r.den_pos; omega

/-─────────────────────────────────────────────────────────────────────────────
  ℝ-level denominator nonzero
─────────────────────────────────────────────────────────────────────────────-/

theorem rational_with_positive_denominator_den_ne_zero
    (r : RationalWithPositiveDenominator) : (r.den : ℝ) ≠ 0 := by
  exact_mod_cast rational_with_positive_denominator_den_nat_ne_zero r

theorem nonnegative_rational_den_ne_zero
    (r : NonnegativeRational) : (r.den : ℝ) ≠ 0 := by
  exact_mod_cast nonnegative_rational_den_nat_ne_zero r

theorem positive_rational_den_ne_zero
    (r : PositiveRational) : (r.den : ℝ) ≠ 0 := by
  exact_mod_cast positive_rational_den_nat_ne_zero r

/-─────────────────────────────────────────────────────────────────────────────
  ℝ-level numerator nonzero (PositiveRational only)

  RationalWithPositiveDenominator has num : Int (signed); no positivity
  or nonnegativity theorem applies in general.
─────────────────────────────────────────────────────────────────────────────-/

theorem positive_rational_num_ne_zero
    (r : PositiveRational) : (r.num : ℝ) ≠ 0 := by
  have h : r.num ≠ 0 := by have := r.num_pos; omega
  exact_mod_cast h

/-─────────────────────────────────────────────────────────────────────────────
  Value semantics
─────────────────────────────────────────────────────────────────────────────-/

theorem positive_rational_toReal_pos
    (r : PositiveRational) : 0 < r.toReal := by
  simp only [PositiveRational.toReal]
  apply div_pos
  · exact_mod_cast r.num_pos
  · exact_mod_cast r.den_pos

theorem nonnegative_rational_toReal_nonneg
    (r : NonnegativeRational) : 0 ≤ r.toReal := by
  simp only [NonnegativeRational.toReal]
  positivity
