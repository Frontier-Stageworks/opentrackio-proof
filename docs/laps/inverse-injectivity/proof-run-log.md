# Proof Run Log — Inverse Injectivity

## Parent theorem

- Theorem / task slug: inverse-injectivity
- File: `inverse_approximation/InverseApproximation.lean` (append-only continuation)
- Command: `/laps-start` (medium task, implementation authorized by user's
  initial prompt, which specified exact theorem shapes)

## Project context

- Same as `docs/laps/bounded-inverse-approximation/proof-run-log.md` — no
  new imports, no new module, no lakefile.toml change.

## Lean command

```sh
lake env lean inverse_approximation/InverseApproximation.lean
lake build InverseApproximation
lake build
```

## Pre-implementation lemma-name verification (done during Stop 1/2 planning)

All confirmed via scratch `exact?`/direct-term checks, recorded in
proof-capsule.md: the `D`-unfold + `linear_combination` algebra identity,
`norm_eq_zero`, the bare-`nlinarith` contraction-forces-zero step, and
`Set.InjOn` composition.

## Verification status

| Check | Command | Result | Notes |
|---|---|---|---|
| Narrow file check | `lake env lean inverse_approximation/InverseApproximation.lean` | pass | 1 warning: unused `hR` in pre-existing `radial_bounded` (not touched this task, same warning as last session) |
| Module build | `lake build InverseApproximation` | pass | `Build completed successfully (3286 jobs)` |
| Full repo build | `lake build` | pass | `Build completed successfully (3316 jobs)` |
| Axiom check | `#print axioms` on all 5 new/promoted theorems | pass | all exactly `[propext, Classical.choice, Quot.sound]` |
| Placeholder grep | `grep -REn "sorry\|admit\|set_option warn\.sorry\|^unsafe\|^partial\|^axiom"` | clean | exit 1, no matches |
| Scope check | `git status --short` | clean | only `inverse_approximation/InverseApproximation.lean` modified; `lakefile.toml`, `Pipeline/`, `DistortionConversion*.lean` untouched |

## Attempts / Failures / Successful hard steps

Implementation order matched the plan exactly: `smul_norm` →
`D_eq_implies_eq` → `D_injective_on_disk` → `inverseStep` →
`inverse_step_maps_disk` → `inverse_step_lipschitz`.

### Failure 1 (only failure this session): `D_eq_implies_eq`'s `hle` step

First draft:
```lean
have hle : ‖a - b‖ ≤ |t| * L θ R * ‖a - b‖ := by
  rw [hnormeq]
  calc |t| * ‖Φ θ a - Φ θ b‖ ≤ |t| * (L θ R * ‖a - b‖) := by gcongr
    _ = |t| * L θ R * ‖a - b‖ := by ring
```
Error: "unsolved goals ... `|t| * L θ R * ‖a - b‖ ≤ |t| * L θ R * (|t| * ‖Φ θ a - Φ θ b‖)`".
Root cause: `rw [hnormeq]` rewrites **every** occurrence of `‖a-b‖` in the
goal `‖a-b‖ ≤ |t|*L θ R*‖a-b‖`, including the one on the RHS I intended to
leave alone — so the calc block (which only proves a statement ending in
`‖a-b‖`) no longer matches the actual (fully double-rewritten) goal.
Classification: wrong-rewrite-direction/scope, not an algebra error — the
inequality itself was never in doubt. Fix: replace the `rw` + `calc` with a
single `calc` starting from `‖a-b‖` and using `hnormeq` as its first step
(`calc ‖a-b‖ = |t|*‖Φθa-Φθb‖ := hnormeq; _ ≤ ...`), which only touches the
LHS occurrence by construction (calc's `_` never revisits the target's own
RHS). Not a repeated path — diagnosed and fixed in one pass, same pattern
avoided in `inverse_step_lipschitz`'s analogous step from the start (calc
starts from the norm expression directly, no blanket `rw` on a two-sided
goal anywhere in this session).

### Successful hard step: the contraction-forces-zero step

`have hzero : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]` closed on
the first attempt, exactly as scratch-verified in proof-capsule.md before
any Lean code — `nlinarith` found the "nonneg number below itself scaled by
a sub-1 factor must be zero" argument automatically once given `hle` (in
context) and the nonnegativity hint.

## Metrics counters

- Lean runs: 6 incremental narrow checks (one per declaration group added,
  with the one fix inline) + 1 module build + 1 full repo build + 1
  axiom-check run = 9
- Failed tactic attempts: 1 (listed above), resolved on the next attempt
- Repeated tactic paths: 0
- Algebra stops: 0
- Proof stops: 0
- Conceptual stops: 0
- Human interventions: 0
- Helper lemmas added: 1 (`smul_norm`, as planned)

---

(Log entries appended chronologically below.)
