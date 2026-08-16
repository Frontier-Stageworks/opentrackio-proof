# Proof Run Log — Local Existence and Uniqueness

## Parent theorem

- Theorem / task slug: inverse-existence
- File: `inverse_approximation/InverseApproximation.lean` (append-only continuation)
- Command: `/laps-start` (medium task)

## Pre-integration scratch validation (see proof-plan.md for full code)

- Attempt 1: `congrArg Subtype.val hzs'` at the final line — type mismatch
  (`z = w` produced, `w = z` expected by `∃!`'s uniqueness clause).
  Classification: wrong direction, not a deeper issue.
- Attempt 2: added `.symm` — compiled clean (2 warnings only: unused `hR`,
  unused `simp` arg `restrict_apply`, both benign).
- Scratch file deleted after validation (not committed) — the validated
  code is preserved verbatim in proof-plan.md for the real-file integration.

## Lean command

```sh
lake env lean inverse_approximation/InverseApproximation.lean
lake build InverseApproximation
lake build
```

## Verification status

| Check | Command | Result | Notes |
|---|---|---|---|
| Narrow file check | `lake env lean inverse_approximation/InverseApproximation.lean` | pass | 1 warning: unused `hR` in pre-existing `radial_bounded` (not this task) |
| Module build | `lake build InverseApproximation` | pass | `Build completed successfully (3286 jobs)` |
| Full repo build | `lake build` | pass | `Build completed successfully (3316 jobs)` |
| Axiom check | `#print axioms D_exists_unique_preimage` | pass | `[propext, Classical.choice, Quot.sound]` |
| Placeholder grep | `grep -REn "sorry\|admit\|..."` | clean | exit 1 |
| Scope check | `git status --short` | clean | only `InverseApproximation.lean` modified (append), no new directory, no `lakefile.toml` change |

## Attempts / Failures / Successful hard steps (real file)

Real-file integration needed exactly 2 fixes, both surfaced immediately by
the narrow Lean check and neither a repeat of the same failure — well
within the user's 2-3-iteration time-box for a single sticking point (and
these were two *different* sticking points, not one point requiring 2-3
attempts):

### Failure 1: `hiff`'s `linear_combination h` — wrong sign

First draft: `constructor <;> (intro h; simp only [Complex.real_smul] at h
⊢; linear_combination h)`. Error: `ring failed`, residual `z*2 +
t*Φθz*2 - y*2 = 0` (and symmetric residual in the other branch) —
i.e. exactly double the target, confirming a sign error (coefficient
should be `-1`, not `+1`; `linear_combination h`'s ring check computes
`goal_lhs - goal_rhs - 1*(h_lhs - h_rhs)`, and with the wrong sign this
equals `2×(target)` instead of `0`). Root cause: the scratch test never
exercised this specific `hiff` lemma (it wasn't needed there — the scratch
test's `f z = z` conclusion IS the fixed-point condition directly, no
translation step), so this was new, untested surface in the real
integration, not a repeat of a previously-solved problem. Fix: `linear_combination -h` in both branches (confirmed by hand: recomputing
the residual with coefficient `-1` gives exactly `0` in both directions).

### Failure 2: `Unknown identifier MapsTo`

The scratch test had `open Set` at file scope (line 4), silently making
`MapsTo` resolve to `Set.MapsTo`. This was NOT carried into the real file
(and should not be — a blanket `open Set` for the whole
`InverseApproximation.lean` file risks unrelated ambiguity with other
identifiers used across the file's 20+ prior declarations, so it was
correctly not added). Root cause: an artifact of the scratch test's
convenience import, not a genuine API mismatch. Fix: qualified both bare
uses (`Set.MapsTo` in the type annotation, `Set.MapsTo.restrict` in a
`simp only` lemma list) explicitly; all other uses were already via dot
notation on a term (`hMapsTo.restrict`, `hContract.exists_fixedPoint'`),
which resolves regardless of `open Set`.

Both fixes applied together, re-checked once — passed. Total: 1 narrow
Lean run with 2 co-occurring errors, both diagnosed and fixed in a single
pass (not 2 separate iterate-and-fail cycles).

## Metrics counters

- Lean runs: 2 (1 fail with 2 co-located errors, 1 pass) for the real file;
  2 more for the pre-integration scratch validation; +1 module build, +1
  full repo build, +1 axiom check = 7 total this session
- Failed tactic attempts: 2 (1 scratch, 1 real-file run containing 2
  co-located errors — counted as the run, not doubled)
- Repeated tactic paths: 0
- Algebra stops: 0
- Proof stops: 0
- Conceptual stops: 0
- Human interventions: 0
- Time-box status: not triggered — total friction across both scratch and
  real-file work was 3 distinct fixes (1 scratch direction mismatch, 1
  real-file sign error, 1 real-file namespace issue), each diagnosed and
  resolved in the immediately following attempt, well under the "2-3
  iterations of a *single* sticking point" threshold for any one of them

---

(Log entries appended chronologically below.)
