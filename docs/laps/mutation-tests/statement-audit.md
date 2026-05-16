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

---

# Statement Audit — buggy_projection_offset_missing_center_inconsistent

## Theorem text

```lean
theorem buggy_projection_offset_missing_center_inconsistent
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : ΔPx = (w / w_shader) * cx) :
    False
```

## Classification

**Direct contradiction** — This wrong formula (missing the centering term `-w_shader/2`)
is unconditionally inconsistent under `w ≠ 0`, `w_shader ≠ 0`.
Proved in `PrincipalPointConversion` as `buggy_principal_point_conversion_inconsistent`.
This theorem delegates to that existing proof.

## Audit

| Check | Result |
|-------|--------|
| Vacuity? | No — `buggy_principal_point_conversion_inconsistent` already establishes satisfiability is impossible |
| Overclaims? | No — direct contradiction is correct here per the paper |
| Delegation valid? | Yes — same parameters, same hypotheses |

---

# Statement Audit — wrong_projection_offset_unscaled_inconsistent

## Theorem text

```lean
theorem wrong_projection_offset_unscaled_inconsistent
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hnot : cx ≠ (w / w_shader) * (cx - w_shader / 2))
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : ΔPx = cx) :
    False
```

## Classification

**Contradiction under anti-degeneracy** — layer 2 of section B.
The anti-degeneracy hypothesis is exactly the negation of the forced equality
derived in layer 1. No extra assumptions needed.

## Audit

| Check | Result |
|-------|--------|
| Vacuous? | No — hnot is satisfiable (e.g. cx=0, w=2, w_shader=1 → forced eq is 0 = -1, so hnot holds) |
| Over-strong? | No — hnot is the minimal negation of the forced equality |
| Proxy? | No |

---

# Statement Audit — wrong_projection_offset_minus_half_forces_degenerate_relation

## Theorem text

```lean
theorem wrong_projection_offset_minus_half_forces_degenerate_relation
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : ΔPx = cx - w_shader / 2) :
    cx - w_shader / 2 = (w / w_shader) * (cx - w_shader / 2)
```

## Classification

**Forces degeneracy** — layer 1 of section C. The wrong formula is not universally
inconsistent; it forces the principal-point offset `cx - w_shader/2` to be a fixed
point of the scale `w/w_shader`.

## Derivation sketch

`principal_point_conversion_necessary` gives `ΔPx = (w/w_shader)*(cx - w_shader/2)`.
Rewrite with `hbug` → conclusion. Closed by `linarith`.

---

# Statement Audit — wrong_projection_offset_minus_half_inconsistent

## Theorem text

```lean
theorem wrong_projection_offset_minus_half_inconsistent
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hnot : cx - w_shader / 2 ≠ (w / w_shader) * (cx - w_shader / 2))
    (hconsist : ∀ x : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2)
    (hbug : ΔPx = cx - w_shader / 2) :
    False
```

## Classification

**Contradiction under anti-degeneracy** — layer 2 of section C.
`hnot` is the negation of the forced equality. Proof: call layer 1 and apply `hnot`.

## Authorization

All four section A/B/C statements approved. No clarification needed.
