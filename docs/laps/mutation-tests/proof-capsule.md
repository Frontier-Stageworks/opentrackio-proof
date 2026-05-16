---
name: mutation-tests-capsule
description: Proof capsule for MutationTests.lean — mutation rejection theorems for OpenCV→OpenTrackIO parameter conversion
metadata:
  type: project
---

# Proof Capsule — MutationTests.lean

## Theorem cluster

A set of Lean 4 theorems proving that plausible wrong formulas are rejected by
the existing semantic consistency conditions. Each mutation theorem shows the
existing positive iff theorems are meaningful — not just definitions that pass
Lean by construction.

## Current narrow scope

**Only one theorem is in scope right now:**

```lean
wrong_projection_offset_unscaled_forces_degenerate_relation
```

All other mutations (radial, tangential, focal-length, swaps, sanity examples)
are deferred until this theorem compiles and is reviewed.

## Intended claim (current theorem)

Given the 1D principal-point consistency condition for all x, plus the wrong
formula ΔPx = cx (unscaled, missing the w/w_shader factor and the centering
term), derive that cx must satisfy the degenerate equality:

```
cx = (w / w_shader) * (cx - w_shader / 2)
```

This is a "forces degeneracy" theorem, not a direct contradiction.

## Objects and parameters

- `w w_shader fx cx F ΔPx : ℝ`
- `hw : w ≠ 0`
- `hw_s : w_shader ≠ 0`
- `hconsist : ∀ x : ℝ, fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2`
- `hbug : ΔPx = cx`

## Conclusion

```lean
cx = (w / w_shader) * (cx - w_shader / 2)
```

## Existing theorems to use

- `principal_point_conversion_necessary` — from consistency derives both
  `F = (w / w_shader) * fx` and `ΔPx = (w / w_shader) * (cx - w_shader / 2)`
- `principal_point_conversion_iff` — iff version (can use .mp direction)

Do not reprove these from scratch.

## Allowed changes

- Local `have` statements
- `obtain` to destructure conjunction from `principal_point_conversion_necessary`
- `linarith` / `nlinarith` / `field_simp` for arithmetic closure
- `rw` with `hbug`

## Forbidden changes

- `sorry`, `admit`, `axiom`, `unsafe`, `partial`
- Weakening the conclusion
- Adding unauthorized hypotheses
- Broad `simp` without explicit lemma list
- Global `[simp]`, `[grind]`, or `grind_pattern`
- Reproving the principal-point theorems from scratch

## Semantic risks

None identified for this theorem — the statement precisely matches the
"forces degeneracy" two-layer pattern required by the task.
The conclusion is a necessary consequence, not a proxy property.
