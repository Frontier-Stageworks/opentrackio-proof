---
name: mutation-tests-proof-plan
description: Proof plan for wrong_projection_offset_unscaled_forces_degenerate_relation
metadata:
  type: project
---

# Proof Plan — wrong_projection_offset_unscaled_forces_degenerate_relation

## Goal shape

```
cx = (w / w_shader) * (cx - w_shader / 2)
```

A linear equality in cx, w, w_shader.

## Opening move

```lean
obtain ⟨_, hΔPx⟩ :=
  principal_point_conversion_necessary w w_shader fx cx F ΔPx hw hw_s hconsist
```

**Why:** `principal_point_conversion_necessary` takes exactly `(hconsist : ∀ x, ...)` plus `hw` and `hw_s` and returns a conjunction. The second component `hΔPx : ΔPx = (w / w_shader) * (cx - w_shader / 2)` is what we need. The first component (the F equation) is discarded with `_`.

## Expected hard step

After `obtain`, we have:
- `hbug : ΔPx = cx`
- `hΔPx : ΔPx = (w / w_shader) * (cx - w_shader / 2)`

The goal `cx = (w / w_shader) * (cx - w_shader / 2)` follows by `linarith`.

## Automation budget

- `obtain` — structural, no search
- `linarith [hbug, hΔPx]` — linear arithmetic, deterministic

No `simp`, no `nlinarith`, no `ring` needed.

## File structure plan

`MutationTests.lean` in `opencv_opentrackio_proofs/`:
```lean
import Mathlib.Tactic
import PrincipalPointConversion

theorem wrong_projection_offset_unscaled_forces_degenerate_relation ... := by
  obtain ⟨_, hΔPx⟩ :=
    principal_point_conversion_necessary w w_shader fx cx F ΔPx hw hw_s hconsist
  linarith
```

## lakefile.toml addition needed

```toml
[[lean_lib]]
name = "MutationTests"
srcDir = "opencv_opentrackio_proofs"
```

## Stop condition

If `linarith` does not close after two attempts:
- Record exact goal and hypotheses in proof-run-log.md
- Emit PROOF STOP
- Do not try algebra spirals
