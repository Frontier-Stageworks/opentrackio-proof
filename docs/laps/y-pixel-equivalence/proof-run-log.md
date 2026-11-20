---
name: y-pixel-equivalence-run-log
description: Proof run log for the y-pixel pipeline equivalence slice
metadata:
  type: project
---

# Proof Run Log — Y-Pixel Pipeline Equivalence

## Session 1

**Setup:** Lean 4.29.0, Mathlib v4.29.0 (pinned, per `lakefile.toml`). Writing three new files per `proof-plan.md`: `Pipeline/PixelSufficiencyY.lean`, `Pipeline/PixelIffHelpersY.lean`, `Pipeline/PixelIffY.lean`, plus y-axis mutation-test analogs.

Entries below are appended as each file is attempted and built.

### PixelSufficiencyY.lean

- Written per proof-plan.md exactly: axis-invariant `h_num`/`h_den` copied verbatim, final `rw [...]; field_simp [...]; ring`.
- `lake build PipelineEquivalence` — succeeded first attempt, 0 errors.
- Only warning: `unused variable 'hF_pos'` at the theorem's hypothesis list — identical pre-existing warning pattern on the sibling x-theorem (`PixelSufficiency.lean:34`), not a new issue introduced here. `hF_pos` is kept in the signature for parity with `opencv_openlensio_full_pipeline_pixel_iff`'s hypothesis list (which the sufficiency theorem's hypotheses must match exactly, since the iff theorem's ← direction calls it directly with the same argument list).
- No algebra tripwire triggered. No deviation from proof-plan.md.

### PixelIffHelpersY.lean — attempt 1 (failed, 2 errors)

**Error 1 — `tangential_gap_forces_scale_y`, `norm_num at h10` branch:**
- Exact first error (verbatim): `Application type mismatch: The argument h10 has type fy - h_shader / h = 0 ∨ p1 = 0 but is expected to have type ?m.167 * ?m.168 = 0 in the application mul_eq_zero.mp h10`
- Goal shape at that point: `False`, via case split on `p1 ≠ 0`.
- Relevant hypotheses: `h10 : fy - h_shader / h = 0 ∨ p1 = 0` (already a disjunction).
- Failure classification: type mismatch (the anticipated wrinkle flagged in proof-plan.md — `norm_num` closed further than `simp only` would have, applying `mul_eq_zero` itself and producing the disjunction directly, rather than leaving a bare product equation for `mul_eq_zero.mp` to consume).
- Why the attempted tactic didn't match the goal: `mul_eq_zero.mp` expects a `_*_=0` hypothesis; `h10` is already the post-`mul_eq_zero` disjunction, so applying `.mp` again is a type error.
- Specific next justified move: replace `rcases mul_eq_zero.mp h10 with hc | hp1z` with `rcases h10 with hc | hp1z` directly (skip the redundant `mul_eq_zero.mp` call) — `norm_num` already did that step.

**Error 2 — `pixel_eq_implies_tangential_gap_y`, local hypothesis name collision:**
- Exact first error (verbatim): `Application type mismatch: The argument h has type ∀ (x' y' : ℝ), ... of sort Prop but is expected to have type ℝ of sort Type in the application h_shader / h`
- Goal shape: n/a — this is a signature-level naming collision, not a tactic failure.
- Relevant hypotheses: the theorem has a parameter `(h : ℝ)` (sensor height, mirroring the project's established `h, h_shader` naming) AND a separately-intended hypothesis parameter also named `h` (the universal pixel-equality hypothesis, mirroring the x-version's `pixel_eq_implies_tangential_gap`'s `(h : ∀ x' y', ...)`). The second declaration shadows the first; every subsequent use of `h` as "sensor height" inside the proof body (e.g. `h_shader / h`) now resolves to the shadowing Prop-typed hypothesis instead.
- Failure classification: theorem statement mismatch (naming collision, not an algebra/tactic issue) — anticipated risk of reusing the x-file's hypothesis name `h` verbatim without checking it against the y-file's own parameter list, where `h` already means something else (sensor height) due to the project's established `h, h_shader` y-axis convention (`principal_point_conversion_2d_iff`). The x-file has no such collision because its sensor-dimension variable is named `w`, not `h`.
- Why the attempted tactic didn't match: not a tactic issue — a direct mirror of the x-file's parameter name `h` for the pixel-equality hypothesis was invalid in this file specifically because `h` was already taken.
- Specific next justified move: rename the pixel-equality hypothesis parameter from `h` to `hpx` (short for "pixel hypothesis") throughout `pixel_eq_implies_tangential_gap_y`, and update its one call site accordingly. No other hypothesis names collide (checked: `hh`, `hhs`, `hF`, `hl1..hl6`, `hq1`, `hq2`, `hF_eq`, `hΔPy`, `hden` are all distinct from the theorem's own parameter list).
- Both fixes applied; rebuilt.

### PixelIffHelpersY.lean — attempt 2 (failed, 1 error)

**Error — `pixel_eq_implies_tangential_gap_y`, `rw [h_rad, h_tang] at hspec`:**
- Exact first error (verbatim): `Tactic 'rewrite' failed: Did not find an occurrence of the pattern` (at line 135:13).
- Goal shape / hypotheses at failure: `h_rad` had already rewritten successfully (the displayed `hspec` context shows the radial term already in `... * y' * F` form); `h_tang`'s pattern — `q1 * ((F*x')^2+(F*y')^2+2*(F*y')^2) + 2*q2*(F*x')*(F*y')` as one combined sum — was not found as a literal subterm.
- Failure classification: wrong rewrite direction / pattern-matching mismatch — specifically an **associativity mismatch**. The surrounding expression parses left-associatively as `(A + q1term) + 2q2term`, so `q1term + 2q2term` is never a literal subterm, even though each individual summand is.
- Why the attempted tactic did not match the goal: I combined both tangential sub-facts into a single `tangential_scaled_eq_y` lemma proving the whole sum at once, unlike the x-version's `PixelIffHelpers.lean`, which keeps `h_tang1`/`h_tang2` as two separate single-term facts specifically so each is individually rewritable against left-associative `+`. My combined lemma can't be used as a single `rw` target against this expression shape.
- Specific next justified move: split `tangential_scaled_eq_y` into two separate lemmas mirroring the x-file exactly — `tangential_scaled_eq_y_squared` (the `q1`/squared-term half) and `tangential_scaled_eq_y_cross` (the `2*q2`/cross-term half) — and rewrite with both individually, same as the x-version's `h_tang1`/`h_tang2` pattern. This is a direct consequence of not having mirrored the x-file's lemma granularity closely enough on the first attempt, not a new algebraic finding.

### PixelIffHelpersY.lean — attempt 3 (succeeded)

- Split into `tangential_scaled_eq_y_sq` / `tangential_scaled_eq_y_cross`, updated the two call sites and the `rw [h_rad, h_tang1, h_tang2] at hspec` line accordingly.
- `lake build PipelineEquivalence` — 0 errors. Warnings only: unused `hden` in `radial_ratio_scaled_eq_y`, unused `hh`/`hhs` in `principal_offset_cancels_y` — same warning pattern as the x-sibling's `radial_ratio_scaled_eq` / `principal_offset_cancels` (both have analogous unused-hypothesis warnings), not new issues.
- File complete: `radial_ratio_scaled_eq_y`, `tangential_scaled_eq_y_sq`, `tangential_scaled_eq_y_cross`, `principal_offset_cancels_y`, `tangential_gap_forces_scale_y`, `pixel_eq_implies_tangential_gap_y` all proved, no `sorry`/`admit`.

### PixelIffY.lean

- Proactively caught (before building) the same `h`-name collision as `pixel_eq_implies_tangential_gap_y`'s earlier failure: the → direction's `intro h` would have shadowed the theorem's own `(h : ℝ)` sensor-height parameter. Renamed to `intro hpx` before the first build attempt, since the failure mode was already understood from the helpers file.
- `lake build PipelineEquivalence` — succeeded first attempt (after the proactive rename), 0 errors, no new warnings.
- `opencv_openlensio_full_pipeline_pixel_iff_y` complete, both directions proved, no `sorry`/`admit`. Composition of `PixelSufficiencyY` (← direction) and the two `PixelIffHelpersY` lemmas (→ direction) — no new algebraic content in this file, as planned.

### MutationTestsY.lean — attempt 1 (failed, 1 error; core lemmas succeeded)

- `whole_tangential_field_iff_y` and `wrong_q1_power_F4_forces_power_degeneracy_y`/`_inconsistent_y` all built cleanly (only benign unused-simp-arg lints, same category as elsewhere in the project).
- **Error — `wrong_q1_paired_with_p2_forces_coincidence_y`:** `linarith failed to find a contradiction` at line 99.
- Goal/hypotheses at failure: `heq : p1 = p2` was already present in context (produced by an inner `field_simp at heq` I had nested inside the final `exact`), but the surrounding `exact mul_left_cancel₀ (inv_ne_zero hF2) (by field_simp at heq; linarith)` was needlessly convoluted — I wrapped an already-fully-reduced fact (`p1 = p2`) inside an unnecessary `mul_left_cancel₀` application that doesn't correspond to the actual goal shape, and the inner `linarith` had nothing left to do once `field_simp` had already closed `heq` to the exact goal.
- Failure classification: automation too broad/opaque — self-inflicted complexity, not a genuine algebraic obstruction. The correct proof is direct: once `heq : p1/F² = p2/F²` is established, `field_simp at heq` alone reduces it to `p1 = p2` (same nonzero denominator on both sides), which is already the theorem's goal.
- Specific next justified move: replace the final two lines with `have heq : p1 / F ^ 2 = p2 / F ^ 2 := by rw [← hq1, hwrong]; field_simp at heq; exact heq` — no `mul_left_cancel₀`/`inv_ne_zero` needed at all.

### MutationTestsY.lean — attempt 2 (succeeded)

- Applied the simplified fix; also tightened the `simp only` argument lists per the earlier unused-arg lints (`mul_zero, mul_one, add_zero` only — dropped `zero_mul`, `zero_add` which Lean flagged as not firing).
- `lake build MutationTestsY` — 0 errors, 0 warnings.
- All 5 theorems proved: `whole_tangential_field_iff_y` (local extraction lemma), `wrong_q1_power_F4_forces_power_degeneracy_y` + `_inconsistent_y` (wrong F-power discrimination), `wrong_q1_paired_with_p2_forces_coincidence_y` + `_inconsistent_y` (coefficient-swap discrimination). Satisfies the MAPS handoff's "at least 2" requirement with both requested categories covered.

### Final verification

- `lake build` (full project, all targets) — succeeded, 3316 jobs (up from the pre-existing 3300-job baseline — consistent with exactly the new modules added).
- `grep` across all 4 new files for `sorry`/`admit`/`axiom`/`unsafe`/`partial`/sorry-suppression options — none found.
- Tactic Source Check: all tactics used (`intro`, `have`, `rw`, `field_simp`, `ring`, `pow_ne_zero`, `div_ne_zero`, `mul_eq_zero`, `linarith`, `norm_num`, `simp only`, `constructor`, `rcases`, `linear_combination`, `obtain`, `mul_left_cancel₀`, `div_eq_div_iff`) are Lean 4 core / Mathlib only — no custom tactics, no metaprogramming, no authorization needed.
- No theorem statement was changed from what `proof-capsule.md`/`proof-plan.md` specified, except the mutation-test theorem names (finalized during writing, not pre-committed in the plan) and the `h`→`hpx` hypothesis-name fix (a name-only change, not a statement change).
