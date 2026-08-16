---
name: inverse-approx-error-proof-plan
description: Proof plan for inverse_approx_error_vs_preimage and inverse_approx_exists_unique_with_error, including the scratch-test plan for the division step
metadata:
  type: project
---

# Proof Plan — Approximate-Inverse Error Relative to a True Preimage

## `inverse_approx_error_vs_preimage`

Exact tactic-level plan, following `statement-audit.md`'s verified chain:

```lean
theorem inverse_approx_error_vs_preimage
    (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R)
    (hcontract : |t| * L θ R < 1)
    (y z : ℂ) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) (hDz : D θ t z = y) :
    ‖U θ t y - z‖ ≤ (|t| ^ 2 * L θ R * M θ R) / (1 - |t| * L θ R) := by
  -- Step 1: z = inverseStep θ t y z, from hDz
  have hzeq : z = inverseStep θ t y z := by
    unfold D at hDz; unfold inverseStep
    simp only [Complex.real_smul] at hDz ⊢
    linear_combination -hDz
  -- Step 2: U θ t y = inverseStep θ t y y (definitional)
  have hUeq : U θ t y = inverseStep θ t y y := by unfold U inverseStep
  -- Step 3: apply inverse_step_lipschitz at (a,b) = (y,z)
  have hA : ‖U θ t y - z‖ ≤ |t| * L θ R * ‖y - z‖ := by
    rw [hUeq, hzeq]  -- careful: only rewrite the OCCURRENCES that need it,
                      -- not blanket rw on a two-sided goal (session history:
                      -- this exact mistake happened in D_eq_implies_eq)
    exact inverse_step_lipschitz θ R t hR y y z hy hz
  -- Step 4/C: phi_bounded at y and at z
  have hCz : ‖y - z‖ ≤ ... -- NOT used directly in the prescribed route;
                            -- (D) below supersedes it. Keep step 4's
                            -- ‖y-z‖ bound out of the final proof to avoid
                            -- accidentally taking the "tighter bound"
                            -- shortcut (AMB-IAE-001) when the task asks
                            -- for the prescribed route specifically.
  have hC : ‖y - U θ t y‖ ≤ |t| * M θ R := by
    rw [hUeq]; unfold inverseStep
    -- ‖y - (y - t•Φθy)‖ = ‖t•Φθy‖ = |t|*‖Φθy‖ ≤ |t|*M θ R
    ...
  have hD : ‖y - z‖ ≤ |t| * M θ R + ‖U θ t y - z‖ := by
    calc ‖y - z‖ ≤ ‖y - U θ t y‖ + ‖U θ t y - z‖ := norm_sub_le_norm_sub_add_norm_sub -- confirm exact name
      _ ≤ |t| * M θ R + ‖U θ t y - z‖ := by gcongr
  have hL_nonneg : (0:ℝ) ≤ L θ R := by unfold L; positivity
  have hq_nonneg : (0:ℝ) ≤ |t| * L θ R := mul_nonneg (abs_nonneg t) hL_nonneg
  have hkey : (1 - |t| * L θ R) * ‖U θ t y - z‖ ≤ |t| * (|t| * L θ R * M θ R) := by
    nlinarith [hA, hD, hq_nonneg]
  have h1mq_pos : (0:ℝ) < 1 - |t| * L θ R := by linarith [hcontract]
  rw [ge_iff_le, div_le_iff₀ h1mq_pos] at * -- or le_div_iff₀; confirm exact
                                             -- direction/name during scratch test
  ...
```

This is a SKETCH with deliberate gaps (`...`) — the exact tactic for the
triangle-inequality lemma name and the final division step are the two
places flagged as friction risks; both are resolved via scratch-testing
below BEFORE writing into the real file.

## Scratch-test plan (mandatory before touching the real file, per the user's instruction)

Test in isolation, using generic stand-ins for `U θ t y`/`z`/`inverseStep`
distances (plain real numbers `e`, `q`, `c` with the right relationships),
to nail down:

1. The triangle-inequality lemma name for `‖y-z‖ ≤ ‖y-w‖ + ‖w-z‖` (some
   `norm_sub_le`-family lemma with an intermediate point).
2. The exact tactic sequence for going from
   `(1-q)*e ≤ q*c` and `0 < 1-q` to `e ≤ (q*c)/(1-q)` — candidates:
   `le_div_iff₀`, `div_le_iff₀`, or just `nlinarith`/`field_simp` after
   establishing the `have`. Division is the specific step the user flagged
   as highest-risk.

Record the working tactic combination here after the scratch test
succeeds, before writing it into the real file.

## `inverse_approx_exists_unique_with_error`

```lean
theorem inverse_approx_exists_unique_with_error
    (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R)
    (hcontract : |t| * L θ R < 1)
    (y : ℂ) (hy : ‖y‖ + |t| * M θ R ≤ R) :
    ∃! z : ℂ, ‖z‖ ≤ R ∧ D θ t z = y ∧
      ‖U θ t y - z‖ ≤ (|t| ^ 2 * L θ R * M θ R) / (1 - |t| * L θ R) := by
  have hM_nonneg : (0:ℝ) ≤ M θ R := by unfold M; positivity
  have hyR : ‖y‖ ≤ R := by nlinarith [mul_nonneg (abs_nonneg t) hM_nonneg]
  obtain ⟨z, ⟨hzR, hDz⟩, huniq⟩ := D_exists_unique_preimage θ R t hR hcontract y hy
  refine ⟨z, ⟨hzR, hDz, inverse_approx_error_vs_preimage θ R t hR hcontract y z hyR hzR hDz⟩, ?_⟩
  rintro w ⟨hwR, hDw, -⟩
  exact huniq w ⟨hwR, hDw⟩
```

Expected short (this exact shape, ~6 lines) — matches the "should be short"
expectation; the `-` in the `rintro` pattern discards the error-bound
conjunct for `w` since it's not needed for uniqueness (statement-audit.md).

## Automation budget

Pure architecture/algebra, no polynomial estimates reopened. `nlinarith`
for the key rearrangement (one `have`, with `hA`, `hD`, `hq_nonneg` as
explicit hints — matches the pattern already used successfully in
`D_eq_implies_eq`'s `hzero` step in this file). Division handled via a
named Mathlib lemma, confirmed by scratch test, not guessed.
