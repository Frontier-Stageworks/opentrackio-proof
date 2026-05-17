---
name: mutation-tests-proof-run-log
description: Run log for MutationTests.lean mutation theorems
metadata:
  type: project
---

# Proof Run Log — MutationTests.lean

## Run 1 — wrong_projection_offset_unscaled_forces_degenerate_relation

**Date:** 2026-05-16

**Theorem:** `wrong_projection_offset_unscaled_forces_degenerate_relation`

**Attempt 1:**

```lean
obtain ⟨_, hΔPx⟩ :=
  principal_point_conversion_necessary w w_shader fx cx F ΔPx hw hw_s hconsist
linarith
```

**Result:** PASS — `lake env lean opencv_opentrackio_proofs/MutationTests.lean` produced no output (clean).

**Hard step:** None — `linarith` closed immediately from `hbug` and `hΔPx`.

**Notes:** Opening move was correct. `principal_point_conversion_necessary` returns a conjunction; destructuring with `obtain ⟨_, hΔPx⟩` discards the F equation and keeps the ΔPx equation. `linarith` closes the goal `cx = (w / w_shader) * (cx - w_shader / 2)` by substituting `hbug : ΔPx = cx` into `hΔPx`.

---

## Run 2 — buggy_projection_offset_missing_center_inconsistent

**Attempt 1:** Term-mode delegation to `buggy_principal_point_conversion_inconsistent`.

**Result:** PASS (clean).

---

## Run 3 — wrong_projection_offset_unscaled_inconsistent

**Attempt 1:** Term-mode: `hnot (wrong_projection_offset_unscaled_forces_degenerate_relation ...)`.

**Result:** PASS (clean).

---

## Run 4 — wrong_projection_offset_minus_half_forces_degenerate_relation

**Attempt 1:** `obtain ⟨_, hΔPx⟩ := principal_point_conversion_necessary ...` then `linarith`.

**Result:** PASS (clean).

---

## Run 5 — wrong_projection_offset_minus_half_inconsistent

**Attempt 1:** Term-mode: `hnot (wrong_projection_offset_minus_half_forces_degenerate_relation ...)`.

**Result:** PASS (clean).

---

## Run 6 — wrong_focal_length_identity_forces_degeneracy

**Attempt 1:** `obtain ⟨hF, _⟩`, `rw [hbug] at hF`, `mul_right_cancel₀ hfx`, `div_eq_iff`, `linarith`.

**Result:** PASS (clean).

---

## Run 7 — wrong_focal_length_identity_inconsistent

**Attempt 1:** Term-mode: `hne (wrong_focal_length_identity_forces_degeneracy ...)`.

**Result:** PASS (clean).

---

## Run 8 — wrong_focal_length_inverted_inconsistent

**Attempt 1:** `obtain`, `rw [hbug]`, `mul_right_cancel₀`, `div_eq_div_iff`, `nlinarith`
for the factor, `rcases mul_eq_zero` case split, `linarith` on each branch.

**Result:** PASS (clean).

---

## Runs 9–20 — Task 4: Radial wrong-power mutations

All 12 theorems (l1, l3, l5 numerator; l2, l4, l6 denominator; layers 1 and 2 each).

**Proof shape (uniform):**
`obtain` correct coefficient from `whole_radial_polynomial_iff.mp`, `linarith` to equate correct and wrong formula, `div_eq_div_iff` to cross-multiply, `mul_left_cancel₀` to cancel `ki ≠ 0`, `.symm` where needed.

**Layer 2 (all):** Term-mode `hpow (layer-1 ...)`.

**Results:** All PASS (clean). Each checked individually after insertion.

---

## Runs 21–28 — Task 5: Tangential wrong-power mutations

All 8 theorems (q1/F, q1/F^4, q2/F, q2/F^4; layers 1 and 2 each).

**Proof shape (uniform):**
`obtain ⟨hqi, _⟩` or `obtain ⟨_, hqi⟩` from `whole_tangential_field_iff.mp`,
`linarith` to equate correct and wrong formula,
`div_eq_div_iff` cross-multiply, `mul_left_cancel₀` cancel `hpi ≠ 0`, `.symm` as needed.
Layer 2: term-mode `hpow (layer-1 ...)`.

**Results:** All PASS (clean). Checked after each pair of layer-1 + layer-2 theorems.

---

## Runs 29–32 — Task 6: Coefficient-swap mutations

All 4 theorems (radial l1↔k2 swap, tangential q1↔p2 swap; layers 1 and 2 each).

**Proof shape (uniform):**
`obtain` correct coefficient from iff.mp,
`linarith` to equate correct and wrong formula (same denominator),
`div_eq_div_iff hF2 hF2` cross-multiply with equal denominators,
`mul_right_cancel₀ hF2` → coefficient equality.
Layer 2: term-mode `hne (layer-1 ...)`.

**Results:** All PASS (clean).

---

## Runs 33–34 — Task 7: Positive sanity examples

**I.1** Existential witness (parametric): `⟨(w/w_shader)*fx, (w/w_shader)*(cx-w_shader/2), rfl, rfl, fun x => by field_simp [hw, hw_s]; ring⟩`

**I.2** Numeric witness (w=2, w_shader=1, fx=3, cx=4 → F=6, ΔPx=7): `⟨6, 7, by norm_num, by norm_num, fun x => by ring⟩`

**Full check after runs 1–34:** `lake env lean opencv_opentrackio_proofs/MutationTests.lean` — clean (no output).

---

## Runs 35–36 — LAPS review: H.3 gap closure (2026-05-16)

**Gap identified:** LAPS review found that the tangential swap `q2 = p1/F^2` (p1 used
as q2's numerator) was missing. H.2 covered `q1 = p2/F^2` only. The "other half is
symmetric" comment applied to within-parameter direction symmetry, not this cross-parameter
case.

**Theorem added:** `wrong_q2_swapped_p1_forces_equal_coefficients` (H.3 layer 1)

```lean
obtain ⟨_, hq2⟩ := (whole_tangential_field_iff p1 p2 q1 q2 F hF).mp hpoly
have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
have heq : p2 / F ^ 2 = p1 / F ^ 2 := by linarith
exact (mul_right_cancel₀ hF2 ((div_eq_div_iff hF2 hF2).mp heq)).symm
```

Uses second conjunct `hq2` (vs H.2 which uses `hq1`). `.symm` needed because
`mul_right_cancel₀` gives `p2 = p1` and conclusion is `p1 = p2`.

**Theorem added:** `wrong_q2_swapped_p1_inconsistent` (H.3 layer 2)

Term-mode: `hne (wrong_q2_swapped_p1_forces_equal_coefficients ...)`.

**Check command:** `lake env lean opencv_opentrackio_proofs/MutationTests.lean`

**Result:** PASS — clean (no output).

**Total theorems after H.3:** 34 named theorems + 2 anonymous examples = 36 items. All clean. No sorry.
