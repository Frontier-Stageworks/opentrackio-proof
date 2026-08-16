# Proof Run Log — Approximate-Inverse Error Relative to a True Preimage

## Parent theorem

- Theorem / task slug: inverse-approx-error
- File: `inverse_approximation/InverseApproximation.lean` (append-only continuation)
- Command: `/laps-start` (medium task)

## Lean command

```sh
lake env lean inverse_approximation/InverseApproximation.lean
lake build InverseApproximation
lake build
```

## Scratch-test log (mandatory, per user instruction, before real-file edit)

Three tests, all passed on the **first attempt** (only benign
unused-variable warnings, no errors):

```lean
-- Test 1: triangle inequality through an intermediate point
example (y z w : ℂ) : ‖y - z‖ ≤ ‖y - w‖ + ‖w - z‖ := by exact?
-- found: norm_sub_le_norm_sub_add_norm_sub y w z

-- Test 2: generic rearrangement + division
example (e q c : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hA : e ≤ q * (c + e)) :
    e ≤ (q * c) / (1 - q) := by
  have h1mq : (0:ℝ) < 1 - q := by linarith
  have hkey : (1 - q) * e ≤ q * c := by nlinarith
  rw [le_div_iff₀ h1mq]
  linarith [hkey]

-- Test 3: exact shape from the real theorem
example (t L M e : ℝ) (hL : 0 ≤ L) (hcontract : |t| * L < 1)
    (hkey : (1 - |t| * L) * e ≤ |t| * (|t| * L * M)) :
    e ≤ (|t| ^ 2 * L * M) / (1 - |t| * L) := by
  have h1mq : (0:ℝ) < 1 - |t| * L := by linarith
  rw [le_div_iff₀ h1mq]
  nlinarith [hkey]
```

**Result: the division step is NOT the friction point it was flagged as
possibly being.** `le_div_iff₀ h1mq` (turning `e ≤ a/(1-q)` into
`e*(1-q) ≤ a`, given `0 < 1-q`) plus `nlinarith`/`linarith` on the
already-derived `hkey` closes it directly — no `field_simp`, no manual
cross-multiplication. `norm_sub_le_norm_sub_add_norm_sub` supplies the
triangle-inequality step. Both confirmed by `exact?`/direct compilation,
not guessed. Scratch file deleted after validation (not committed); this
log preserves the working code for the real-file integration.

## Verification status

| Check | Command | Result | Notes |
|---|---|---|---|
| Narrow file check | `lake env lean inverse_approximation/InverseApproximation.lean` | pass | 1 warning: unused `hR` in pre-existing `radial_bounded` (not this task) |
| Module build | `lake build InverseApproximation` | pass | `Build completed successfully (3286 jobs)` |
| Full repo build | `lake build` | pass | `Build completed successfully (3316 jobs)` |
| Axiom check | `#print axioms` on both new theorems | pass | both exactly `[propext, Classical.choice, Quot.sound]` |
| Placeholder grep | `grep -REn "sorry\|admit\|..."` | clean | exit 1 |
| Scope check | `git status --short` | clean | only `InverseApproximation.lean` modified (append), no new directory, no `lakefile.toml` change |

## Attempts / Failures / Successful hard steps

### `inverse_approx_error_vs_preimage` — 2 fixes, both minor

**Failure 1**: `have heq : y - U θ t y = t • Φ θ y := by unfold U; abel`
left an unsolved goal `y - t•Φθy = y - t•Φθy` (syntactically trivial, but
`abel` did not close it — the same `unfold X; abel` pattern worked earlier
in this file for `x - D θ t x = -(t•Φθx)`, so this is a shape-specific
quirk, not a general problem with `abel` in this file). Fix: switched to
`unfold U; simp only [Complex.real_smul]; ring`, the same pattern already
proven reliable in `D_exists_unique_preimage`'s `hiff`.

**Failure 2** (same run, co-located): `have hUeq : U θ t y = inverseStep θ t
y y := by unfold U inverseStep` left the same-looking trivial unsolved
goal — `unfold` does not automatically try `rfl` to close a resulting
reflexivity goal. Fix: replaced with `:= rfl` directly (both sides are
definitionally equal without needing an explicit `unfold` at all).

Both fixes applied together, re-checked once — passed. The rest of the
proof (the `hA`/`hC`/`hD'`/`hkey`/final-division chain) compiled exactly as
scratch-tested, with zero further changes.

### `inverse_approx_exists_unique_with_error` — 0 fixes, first attempt

Compiled clean on the first attempt. 6 lines, exactly as planned — matches
the "should be short" expectation from the task prompt.

## Metrics counters

- Lean runs: 2 real-file runs (1 fail with 2 co-located issues in theorem
  1, 1 pass covering both theorems) + 1 scratch run (pass) + 1 module
  build + 1 full repo build + 1 axiom check = 6
- Failed tactic attempts: 2 (both in theorem 1's first real-file attempt,
  fixed together)
- Repeated tactic paths: 0
- Algebra stops: 0
- Proof stops: 0
- Conceptual stops: 0
- Human interventions: 0

---

(Log entries appended chronologically below.)
