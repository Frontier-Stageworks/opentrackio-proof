/-
  Pipeline/SignedCubicBoundsGlobal.lean

  Extends Pipeline/SignedCubicBounds.lean with lemmas for bounding a cubic
  f(u)=au+bu²+cu³ BELOW on an UNBOUNDED range u≥0 — not just on a single
  bounded interval [0,U] as `cubic_tight_pos`/`cubic_tight_neg` do. Needed
  because Azure Kinect DK's actual denominator polynomial dips to a genuine
  interior minimum (at an irrational critical point, found only numerically in
  audit/REAL_CALIBRATION_VALIDATION.md/IMPROVED_REAL_CALIBRATION_BOUNDS.md) and
  then rises without bound — `cubic_tight_neg`'s single-interval monotonicity
  condition cannot cover a range that both decreases AND increases.

  Strategy: f(u) = f(L) + (u-L)·G_L(u), where G_L(u) := a+b(u+L)+c(u²+uL+L²) is
  the "anchored divided-difference" quadratic (G_L(L) = f'(L) exactly). G_L is
  itself a convex (leading coefficient c) quadratic in u whose OWN vertex
  condition (b+3cL≥0, i.e. L is at or past f's own derivative's vertex) makes
  G_L monotonically non-decreasing on [L,∞) — this is PURE ALGEBRA (a
  divided-difference factoring, exactly the same technique used throughout
  Pipeline/SignedCubicBounds.lean), not calculus/Mathlib derivative machinery.

  Two consequences, covering a bounded piece [L,U] and an unbounded tail
  [L,∞) respectively:
  - `cubic_bounded_piece_lower`: f(u) ≥ f(L) + (U-L)·f'(L) for u∈[L,U], valid
    whenever f'(L) ≤ 0 (the "still descending or at the bottom" case).
  - `cubic_tail_lower`: f(u) ≥ f(L) for u≥L, valid whenever f'(L) ≥ 0 (the
    "already ascending" case) — no upper bound needed at all.

  Chaining these (a bounded-interval `cubic_tight_neg` piece near the origin,
  several `cubic_bounded_piece_lower` pieces bracketing the interior minimum,
  then one `cubic_tail_lower` piece once the derivative turns nonnegative)
  gives a genuine GLOBAL lower bound for u≥0 — applied to Azure Kinect DK's
  actual denominator coefficients in Pipeline/KinectGlobalDenominator.lean.

  Does not modify Pipeline/SignedCubicBounds.lean or any other existing file.
  No axioms, no `sorry`.
-/

import Pipeline.SignedCubicBounds

/-- `G_L(u) - G_L(L)`-style divided-difference identity for the cubic, with the
roles of the two evaluation points swapped relative to `cubic_diff_eq_mul`
(reused directly, not reproved). -/
theorem cubic_diff_eq_mul' (a b c L u : ℝ) :
    (a * u + b * u ^ 2 + c * u ^ 3) - (a * L + b * L ^ 2 + c * L ^ 3)
      = (u - L) * (a + b * (u + L) + c * (u ^ 2 + u * L + L ^ 2)) := by
  have h := cubic_diff_eq_mul a b c u L
  linarith [h]

/-- `G_L(u) ≥ G_L(L) = f'(L)` for `u ≥ L`, given the vertex condition `b+3cL≥0`.
Pure algebra: `G_L(u)-G_L(L) = (u-L)·(b+2cL+cu)`, and `b+2cL+cu ≥ b+3cL ≥ 0`
using `u≥L` and `c>0`. -/
theorem Gfun_mono_ge (a b c L : ℝ) (hc : 0 < c) (hvertex : b + 3 * c * L ≥ 0)
    (u : ℝ) (huL : L ≤ u) :
    a + 2 * b * L + 3 * c * L ^ 2 ≤ a + b * (u + L) + c * (u ^ 2 + u * L + L ^ 2) := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ u - L) (by nlinarith : (0:ℝ) ≤ b + 2 * c * L + c * u)]

/-- Bounded-piece lower bound: valid when the cubic's derivative at the LEFT
endpoint `L` is still `≤ 0` (the piece lies within or ends at the interior
dip). -/
theorem cubic_bounded_piece_lower (a b c L U : ℝ) (hc : 0 < c) (hLU : L ≤ U)
    (hvertex : b + 3 * c * L ≥ 0) (hfprimeL : a + 2 * b * L + 3 * c * L ^ 2 ≤ 0)
    (u : ℝ) (huL : L ≤ u) (huU : u ≤ U) :
    a * L + b * L ^ 2 + c * L ^ 3 + (U - L) * (a + 2 * b * L + 3 * c * L ^ 2)
      ≤ a * u + b * u ^ 2 + c * u ^ 3 := by
  have hGge := Gfun_mono_ge a b c L hc hvertex u huL
  have hdiff := cubic_diff_eq_mul' a b c L u
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ u - L) (by linarith [hGge] :
    (0:ℝ) ≤ a + b * (u + L) + c * (u ^ 2 + u * L + L ^ 2) - (a + 2 * b * L + 3 * c * L ^ 2)),
    hdiff, mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ U - u) hfprimeL]

/-- Unbounded tail lower bound: valid once the derivative at `L` is already
`≥ 0` (the cubic is past its interior dip and ascending from here on, forever
— no upper limit needed). -/
theorem cubic_tail_lower (a b c L : ℝ) (hc : 0 < c) (hvertex : b + 3 * c * L ≥ 0)
    (hfprimeL : 0 ≤ a + 2 * b * L + 3 * c * L ^ 2)
    (u : ℝ) (huL : L ≤ u) :
    a * L + b * L ^ 2 + c * L ^ 3 ≤ a * u + b * u ^ 2 + c * u ^ 3 := by
  have hGge := Gfun_mono_ge a b c L hc hvertex u huL
  have hdiff := cubic_diff_eq_mul' a b c L u
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ u - L) (by linarith [hGge, hfprimeL] :
    (0:ℝ) ≤ a + b * (u + L) + c * (u ^ 2 + u * L + L ^ 2)), hdiff]
