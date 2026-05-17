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

## Pending theorems (deferred — do not start without authorization)

- B layer 2: `wrong_projection_offset_unscaled_inconsistent`
- C: `wrong_projection_offset_minus_half_*`
- D: `wrong_focal_length_identity_*`
- E: `wrong_focal_length_inverted_inconsistent`
- F: radial wrong-power (numerator and denominator)
- G: tangential wrong-power
- H: coefficient swaps
- I: sanity examples
