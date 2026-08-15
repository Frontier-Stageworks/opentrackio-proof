# Proof Run Log — Tangential Conversion Physical-Semantics Fix

## Parent theorem

- Theorem / task slug: tangential-conversion-physical-fix
- File: `opencv_opentrackio_proofs/DistortionConversionCorrected.lean`,
  `opencv_opentrackio_proofs/Pipeline/PixelIffCorrected.lean`
- Command: `/laps-start` (medium task, single slice)

## Project context

- Lean toolchain: `leanprover/lean4:v4.29.0` (`lean-toolchain`)
- Package config: `lakefile.toml`
- Mathlib available: yes (cached, confirmed via `lake env lean` on existing file, ~19s)
- Target imports: `Mathlib.Tactic` (via `DistortionConversion`), `DistortionConversion`, `Pipeline.PixelSufficiency`
- Relevant local modules: `DistortionConversion.lean`, `Pipeline/PixelIffHelpers.lean`, `Pipeline/PixelSufficiency.lean`

## Lean command

```sh
lake env lean opencv_opentrackio_proofs/DistortionConversionCorrected.lean
lake env lean opencv_opentrackio_proofs/Pipeline/PixelIffCorrected.lean
lake build DistortionConversionCorrected
lake build PipelineEquivalence
```

## Verification status

| Check | Command | Result | Notes |
|---|---|---|---|
| Narrow file check | `lake env lean opencv_opentrackio_proofs/DistortionConversionCorrected.lean` | pass | 0 warnings |
| Narrow file check | `lake env lean opencv_opentrackio_proofs/Pipeline/PixelIffCorrected.lean` | pass | 1 warning: unused `hF_pos` (see AMB-TCF-002, matches pre-existing pattern in unmodified `PixelSufficiency.lean`) |
| Module build | `lake build DistortionConversionCorrected` | pass | `Build completed successfully (3287 jobs)` |
| Module build | `lake build PipelineEquivalence` | pass | `Build completed successfully (3299 jobs)`; pre-existing warnings in unmodified `PixelSufficiency.lean`/`PixelIffHelpers.lean` observed (unused `hF_pos`, unused `hden`/`hw`/`hws`, unused simp arg `add_zero`) — confirmed NOT introduced by this task, present in baseline files untouched here |

## Attempts / Failures / Successful hard steps

### Attempt 1 (failure): Layer 1 F-cancellation via `linear_combination -h11` / `-h10`

- Goal shape (after `rw [eq_div_iff hF]`): `q1 * F = p1` from hypothesis
  `h11 : F * p1 = q1 * F * F`.
- Tactic tried: `linear_combination -h11`.
- Exact error: `ring failed, ring expressions not equal` — remaining goal
  `q1 * F - q1 * F ^ 2 + F * p1 - p1 = 0`.
- Failure classification: algebra formatting / missing nonzero side condition.
  `linear_combination` only performs pure ring-identity checks; canceling one
  power of F from `F*p1 = q1*F²` down to `p1 = q1*F` requires actual
  division/cancellation using `hF : F ≠ 0`, which is not a ring identity and
  cannot be discharged by any linear combination of the hypothesis alone.
- Mismatch explanation: I initially treated the F-cancellation as a pure ring
  rearrangement; it is not — it needs `mul_right_cancel₀`.
- Was this tactic path already tried? No (first attempt). Not repeated after
  diagnosing — moved to the correct approach below (whole_tangential_field_iff_physical's
  two similar goals also hit this in the same first pass, since I compiled
  the whole file before fixing the first error — three goals in one run, same
  root cause, all fixed together, not a "repeated path" violation since the
  cause was diagnosed once and applied consistently).

### Attempt 2 (success): `mul_right_cancel₀` after a pure-ring rearrangement `have`

```lean
have hcancel : p1 * F = (q1 * F) * F := by linear_combination h11
have hp1eq : p1 = q1 * F := mul_right_cancel₀ hF hcancel
rw [eq_div_iff hF]
exact hp1eq.symm
```

- Why it works: `p1 * F = (q1*F)*F` is a *pure* ring rearrangement of
  `h11 : F*p1 = q1*F*F` (both sides just commuted/associated, no division),
  so `linear_combination h11` (coefficient 1) closes it via `ring`. Then
  `mul_right_cancel₀ hF` performs the one genuine cancellation step using
  `hF : F ≠ 0`, which `ring`/`linear_combination` cannot do on their own.
- Hard step type: algebra solver (`linear_combination`) + delegated theorem
  (`mul_right_cancel₀`) — the two-step split is the hard step here: recognizing
  that F-cancellation is not a ring fact and must be isolated into its own
  `mul_right_cancel₀` application after a ring-only restatement.
- Applied identically to `tangential_q2_conversion_physical`, and to the two
  coefficient-extraction steps inside `whole_tangential_field_iff_physical`'s
  forward direction (`hp2eq` from `h01`, `hp1eq` from `h11` after substituting
  `hp2eq` via `rw`).

### Attempt 3 (failure→success): backward-direction `field_simp [hF2]; ring` → "no goals"

- In `whole_tangential_field_iff_physical`'s and
  `whole_tangential_field_2d_iff_physical`'s backward directions, `field_simp
  [hF2]` fully closed the goal (its internal normalization already reduces the
  substituted equality to a syntactic match), so a following `ring` produced
  `error: No goals to be solved`.
- Failure classification: automation too broad / unnecessary trailing tactic
  (not an algebra failure — `field_simp` over-delivered).
- Fix: removed the trailing `ring` in both backward-direction proofs. Not a
  repeated-path violation — this is dropping a step, not retrying one.

### Successful hard step: pipeline-level `hfx : fx ≠ 0` without `hscale`

The baseline `opencv_openlensio_full_pipeline_pixel_sufficiency` derives
`fx ≠ 0` from `hscale : ws/w = fx` plus `hws : ws ≠ 0`. The corrected theorem
has no `hscale` hypothesis (it isn't assumed and doesn't hold in general — see
AMB-TCF-001), so this derivation path is unavailable. Instead:

```lean
have hfx : fx ≠ 0 := by
  have hF' : (w / ws) * fx ≠ 0 := hF_eq ▸ hF
  exact right_ne_zero_of_mul hF'
```

Why it works: `hF : F ≠ 0` together with `hF_eq : F = (w/ws)*fx` gives
`(w/ws)*fx ≠ 0` directly (rewrite, not derivation from scale-matching), and
`right_ne_zero_of_mul` extracts `fx ≠ 0` from a nonzero product. This is a
strictly more direct route than the baseline's, and required no new
hypothesis — confirming the corrected theorem's hypothesis list (one fewer
hypothesis than the baseline: no `hscale`, no `hp`) is genuinely sufficient.
Compiled successfully on the first attempt.

### Successful hard step: main pixel-equality closing tactic

```lean
rw [h_num, h_den, hq1, hq2, hΔPx, hF_eq]
field_simp [hw, hws, hfx, hden_xy]
ring
```

Compiled on the first attempt (no failed intermediate tries) — the direct
full-substitution style mirroring `opencv_openlensio_full_pipeline_pixel_sufficiency`'s
closing block worked without needing the more modular `h_tang`/`h_scale`
`have`-based approach anticipated in `proof-plan.md`. Recorded as a plan
deviation: the plan anticipated needing an explicit
`tangential_scaled_eq_physical` helper lemma; it was not needed because
`field_simp` + `ring` handled the full substituted expression directly. No
`tangential_scaled_eq_physical` helper was added (plan said "Helper lemmas
added: 0" would only be wrong if this were needed — it wasn't).

## Diagnostics checks

```
DIAGNOSTICS CHECK (DistortionConversionCorrected.lean):
- Narrow Lean command run: lake env lean opencv_opentrackio_proofs/DistortionConversionCorrected.lean
- Result: pass
- Warnings present: no
- Sorry warnings present: no
- `set_option warn.sorry false` in any file: no
- Linter warnings present: no
- Unexpected generated files: no
- UTF-8 BOM or encoding problems: no
- Import changes since last check: yes — new file imports `DistortionConversion` only
- Broad build needed: yes, ran `lake build DistortionConversionCorrected` — pass
- Action before next slice: none
```

```
DIAGNOSTICS CHECK (Pipeline/PixelIffCorrected.lean):
- Narrow Lean command run: lake env lean opencv_opentrackio_proofs/Pipeline/PixelIffCorrected.lean
- Result: pass
- Warnings present: yes — unused variable `hF_pos` (expected, see AMB-TCF-002; matches pre-existing baseline pattern in `PixelSufficiency.lean`, not a new issue)
- Sorry warnings present: no
- `set_option warn.sorry false` in any file: no
- Linter warnings present: yes (the hF_pos one, already noted)
- Unexpected generated files: no
- UTF-8 BOM or encoding problems: no
- Import changes since last check: yes — new file imports `DistortionConversion` only (self-contained, no import of `Pipeline.PixelIffHelpers`/`Pipeline.PixelSufficiency`)
- Broad build needed: yes, ran `lake build PipelineEquivalence` — pass (picked up automatically via existing `Pipeline.+` glob, no lakefile change needed for this file)
- Action before next slice: none
```

## Metrics counters

- Lean runs: 5 (2 narrow checks with fixes in between = effectively 3 narrow
  compile attempts on DistortionConversionCorrected.lean [1 fail, 1 pass] + 1
  on PixelIffCorrected.lean [pass first try] + 2 module builds)
- Failed tactic attempts: 3 (the `linear_combination -h11`/`-h10` sign error,
  counted once per root cause since diagnosed together; the two trailing
  `ring` "no goals" errors, same root cause)
- Repeated tactic paths: 0
- Algebra stops: 0 (root cause diagnosed within the two-failure tripwire
  budget; no `ALGEBRA STOP` needed)
- Proof stops: 0
- Conceptual stops: 0
- Human interventions: 0
- Helper lemmas added: 0 (anticipated `tangential_scaled_eq_physical` turned
  out unnecessary — direct `field_simp`/`ring` sufficed)
- Theorem statement changes requested: 1 — the conclusion shape of
  `opencv_openlensio_full_pipeline_pixel_corrected` (iff → plain equality),
  authorized in `proof-capsule.md`/`ambiguity-register.md` AMB-TCF-001 before
  any tactic code was written (not a post-hoc weakening)
- Definition changes requested: 0

## Placeholder hygiene

- No `sorry`: yes
- No `sorry` replaced with `axiom` or `constant`: yes
- No `set_option warn.sorry false`: yes
- No warning suppression: yes
- Temporary holes documented in this log: none

## Final status

- Lean file check (both new files): pass
- Module build (`DistortionConversionCorrected`, `PipelineEquivalence`): pass
- No `sorry`: yes
- No `admit`: yes
- No unauthorized `axiom`: yes
- No unauthorized `constant`: yes
- No `unsafe`: yes
- No `partial`: yes
- No `set_option warn.sorry false`: yes
- Theorem statement preserved or authorized: yes (all baseline theorems
  untouched; the one statement-shape decision was authorized pre-tactic in
  the capsule/ambiguity register)
- Semantic review complete: see `proof-review.md`
