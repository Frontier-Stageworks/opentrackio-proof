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

## Pending theorems (deferred — do not start without authorization)

- B layer 2: `wrong_projection_offset_unscaled_inconsistent`
- C: `wrong_projection_offset_minus_half_*`
- D: `wrong_focal_length_identity_*`
- E: `wrong_focal_length_inverted_inconsistent`
- F: radial wrong-power (numerator and denominator)
- G: tangential wrong-power
- H: coefficient swaps
- I: sanity examples
