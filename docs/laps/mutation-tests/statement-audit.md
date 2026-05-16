---
name: mutation-tests-statement-audit
description: Statement audit for wrong_projection_offset_unscaled_forces_degenerate_relation
metadata:
  type: project
---

# Statement Audit — wrong_projection_offset_unscaled_forces_degenerate_relation

## Theorem text

```lean
theorem wrong_projection_offset_unscaled_forces_degenerate_relation
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : ΔPx = cx) :
    cx = (w / w_shader) * (cx - w_shader / 2)
```

## Classification

**Forces degeneracy** — not a direct contradiction. The wrong formula ΔPx = cx
is not universally inconsistent; it forces cx to lie on a specific curve
parameterized by w and w_shader.

## Audit checks

| Check | Result |
|-------|--------|
| Vacuous? | No — hconsist and hbug are satisfiable simultaneously (requires specific cx) |
| Over-strong hypotheses? | No — hw and hw_s are needed for field_simp; hconsist drives the derivation |
| Unused hypotheses? | None expected |
| Proxy property? | No — conclusion is exactly the value ΔPx must have per consistency, equated to cx |
| Theorem laundering? | No — uses existing proven theorem, does not restate it |
| Test-shaped? | No — universally quantified over x via hconsist |
| Implementation artifact? | No — pure mathematical claim about coordinate system parameters |
| Unreadable specification? | No |

## Derivation sketch

1. Apply `principal_point_conversion_necessary` to `hconsist` → get
   `hΔPx : ΔPx = (w / w_shader) * (cx - w_shader / 2)`
2. Rewrite with `hbug : ΔPx = cx` →
   `cx = (w / w_shader) * (cx - w_shader / 2)` ✓

The proof is one `obtain` + one `linarith` (or `rw`+`exact`).

## Risk: is the statement too weak?

No. This is the correct two-layer pattern. The second layer
(`wrong_projection_offset_unscaled_inconsistent`) adds the anti-degeneracy
hypothesis and closes to `False`. That theorem is deferred.

## Authorization

Statement approved as-is. No clarification needed.
