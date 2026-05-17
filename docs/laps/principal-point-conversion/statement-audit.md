---
name: principal-point-conversion-statement-audit
description: Statement audit for PrincipalPointConversion.lean — adopted proof
metadata:
  type: project
---

# Statement Audit — PrincipalPointConversion.lean (Adopted)

---

## Theorem 1: `principal_point_conversion_necessary`

### Formal statement

```lean
theorem principal_point_conversion_necessary
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hconsist : ∀ x'' : ℝ,
        fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2) :
    F   = (w / w_shader) * fx  ∧
    ΔPx = (w / w_shader) * (cx - w_shader / 2)
```

### Plain English

If the OpenCV and OpenTrackIO projections agree at every normalised coordinate x'', then F and ΔPx are uniquely determined to be the corrected conversion formulas.

### Audit

| Check | Result |
|-------|--------|
| Vacuous? | No — hconsist is satisfiable; witnesses exist (any w, w_shader, fx, cx determine F and ΔPx) |
| Over-strong hypotheses? | The nonzero hypotheses are justified by denominator-bearing conversion formulas and by the delegated theorem interfaces |
| Unused hypotheses? | None |
| Weakened conclusion? | No — `∧` gives both components; the formulas are exactly what the paper states |
| Proxy property? | No — conclusion is the exact parameter pair, not a weaker consequence |
| Test-shaped? | No — universally quantified over all x'' |

### Classification: **Accepted as-is**

---

## Theorem 2: `principal_point_conversion_iff`

### Formal statement

```lean
theorem principal_point_conversion_iff
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0) :
    (∀ x'' : ℝ,
        fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2) ↔
    F   = (w / w_shader) * fx  ∧
    ΔPx = (w / w_shader) * (cx - w_shader / 2)
```

### Plain English

The 1D consistency condition holds for all x'' if and only if F and ΔPx have exactly the corrected values. This is the strongest possible statement: it characterises the consistency condition completely.

### Audit

| Check | Result |
|-------|--------|
| Vacuous? | No |
| Over-strong? | The nonzero hypotheses are justified by denominator-bearing conversion formulas and by the delegated theorem interfaces |
| Weakened? | No — iff is the strongest form |
| Proxy? | No |

### Classification: **Accepted as-is**

---

## Theorem 3: `principal_point_conversion_2d_iff`

### Formal statement

```lean
theorem principal_point_conversion_2d_iff
    (w h w_shader h_shader fx fy cx cy F ΔPx ΔPy : ℝ)
    (hw   : w ≠ 0) (hh   : h ≠ 0)
    (hw_s : w_shader ≠ 0) (hh_s : h_shader ≠ 0) :
    (∀ x'' y'' : ℝ,
        fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2 ∧
        fy * y'' + cy = (h_shader / h) * (F * y'' + ΔPy) + h_shader / 2) ↔
    F   = (w / w_shader) * fx  ∧
    ΔPx = (w / w_shader) * (cx - w_shader / 2) ∧
    F   = (h / h_shader) * fy  ∧
    ΔPy = (h / h_shader) * (cy - h_shader / 2)
```

### Plain English

The full 2D consistency condition (both u and v pixel coordinates agree for all (x'', y'')) holds iff all four conversion formulas hold — including the shared F constraint from both axes.

### Audit

| Check | Result |
|-------|--------|
| Vacuous? | No |
| Over-strong? | The nonzero hypotheses are justified by denominator-bearing conversion formulas and by the delegated theorem interfaces |
| F appears twice in conclusion? | Yes — `F = (w/w_shader)*fx` AND `F = (h/h_shader)*fy`. This is intentional: the single scalar F must satisfy both axes simultaneously, and the theorem exposes that both constraints are present |
| Weakened? | No — iff |

### Classification: **Accepted as-is**

---

## Theorem 4: `single_focal_length_compatibility`

### Formal statement

```lean
theorem single_focal_length_compatibility
    (w h w_shader h_shader fx fy cx cy F ΔPx ΔPy : ℝ)
    (hw   : w ≠ 0) (hh   : h ≠ 0)
    (hw_s : w_shader ≠ 0) (hh_s : h_shader ≠ 0)
    (hconsist : ∀ x'' y'' : ℝ,
        fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2 ∧
        fy * y'' + cy = (h_shader / h) * (F * y'' + ΔPy) + h_shader / 2) :
    (w / w_shader) * fx = (h / h_shader) * fy
```

### Plain English

If 2D consistency holds, both axes independently determine F, and the two values must agree: `(w/w_shader)*fx = (h/h_shader)*fy`. This is the condition under which an OpenCV calibration (with separate fx, fy) is exactly representable by the single scalar F of the OpenTrackIO model.

### Audit

| Check | Result |
|-------|--------|
| Vacuous? | No — hconsist is satisfiable exactly when the constraint holds |
| Over-strong hypotheses? | The nonzero hypotheses are justified by denominator-bearing conversion formulas and by the delegated theorem interfaces |
| Unused hypotheses? | `cx`, `cy`, `ΔPx`, `ΔPy` appear in hconsist and in the 2D iff theorem — they are formally required by Theorem 3, even though the conclusion mentions only `w`, `w_shader`, `h`, `h_shader`, `fx`, `fy`. This is not over-strong: the 2D iff theorem's interface requires all parameters |
| Weakened conclusion? | No — the conclusion is exactly the single-F compatibility condition |
| One-way implication? | Correct — the converse (compatibility → 2D consistency) would be false in general (compatibility is necessary but not sufficient; ΔPx and ΔPy also need to be correct) |

### Note on parameter bloat

`cx`, `cy`, `ΔPx`, `ΔPy` are in the signature but do not appear in the conclusion. They are required because the proof delegates to `principal_point_conversion_2d_iff`, which carries all parameters. This is not an anti-pattern for an adopted proof — it is a consequence of the proof strategy. A refactor could existentially quantify these out or add a helper, but the current form is correct and not misleading.

### Classification: **Accepted with notes** (parameter bloat; see note above)

---

## Theorem 5: `buggy_principal_point_conversion_inconsistent`

### Formal statement

```lean
theorem buggy_principal_point_conversion_inconsistent
    (w w_shader fx cx F ΔPx : ℝ)
    (hw   : w ≠ 0)
    (hw_s : w_shader ≠ 0)
    (hconsist : ∀ x'' : ℝ,
        fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2)
    (hbug : ΔPx = (w / w_shader) * cx) :
    False
```

### Plain English

The old buggy formula `ΔPx = (w/w_shader)*cx` (missing the centering term `-w_shader/2`) cannot satisfy the consistency condition under any nonzero `w` and `w_shader`. It is not just imprecise — it is mathematically incompatible.

### Audit

| Check | Result |
|-------|--------|
| Vacuous? | Not vacuous in the bad sense: the theorem intentionally proves that this pair of assumptions is inconsistent. This is a regression contradiction theorem, not a semantic preservation theorem. |
| Over-strong hypotheses? | The nonzero hypotheses are justified: `hw` and `hw_s` are required to derive `w/w_shader ≠ 0`, which is the key step in the contradiction |
| Weakened? | No — concludes `False`, the strongest possible regression claim |
| Proxy property? | No |
| Direct contradiction correct? | Yes — the analysis in `MutationTests.lean` confirms this is genuinely unconditional (no anti-degeneracy hypothesis needed), unlike the other mutation theorems |

### Classification: **Accepted as-is**
