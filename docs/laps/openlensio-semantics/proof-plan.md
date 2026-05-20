---
name: proof-plan
description: Stop 2 Proof Plans for all openlensio_semantics slices — goal shape, opening move, hard step, automation budget
metadata:
  type: reference
---

# Proof Plans — `openlensio_semantics`

One section per theorem-bearing slice.

---

## SLICE-OL-04 — `sensorRadius_nonneg`

### Goal shape

`0 ≤ Real.sqrt (p.x ^ 2 + p.y ^ 2)`

Classification: **order** — nonneg of a `Real.sqrt` application.

### Opening move

`Real.sqrt_nonneg _` — this is a direct Mathlib lemma. The goal unfolds to exactly this shape after `simp [sensorRadius]` or `unfold sensorRadius`.

### Why it fits

`Real.sqrt` in Mathlib satisfies `∀ x, 0 ≤ Real.sqrt x`. The argument `p.x^2 + p.y^2` does not need to be nonneg explicitly — `Real.sqrt_nonneg` holds for all real inputs.

### Expected hard step

None.

### Automation budget

One tactic: `exact Real.sqrt_nonneg _` after unfolding `sensorRadius`, or the proof term `Real.sqrt_nonneg _` directly.

### Helper lemmas needed

None.

---

## SLICE-OL-03 — `semanticExtraction_sound`

### Goal shape

`ValidLensSemantics s` where `ValidLensSemantics l = (0 < l.focalLength)`.

The hypothesis `h` contains the if-expression from `extractLensSemantics`.

Classification: **implication** — from Except success condition to a validity predicate.

### Opening move

`unfold extractLensSemantics at h` — exposes the `if _ : 0 < focalLength then .ok {...} else .error ...` structure. Then `split_ifs at h with hf` to case-split on the if condition.

### Why it fits

The definition of `extractLensSemantics` is a single if-then-else. Unfolding and splitting mirrors the definition exactly. The positive branch gives `hf : 0 < focalLength` directly; the negative branch yields a type contradiction.

### Case analysis

**Positive branch:**
- After `split_ifs`, `h : Except.ok { focalLength := focalLength, ... } = Except.ok s`
- `simp only [Except.ok.injEq] at h` injects and performs `subst_eqs`, substituting `s` with the record literal
- `subst h` explicitly finishes substitution
- Goal becomes `0 < focalLength` — closed by `exact hf`

**Negative branch:**
- After `split_ifs`, `h : Except.error .nonPositiveFocalLength = Except.ok s`
- This is a type contradiction; `split_ifs` auto-closes it — no tactic needed

### Expected hard step

None. The proof follows directly from the if-guard structure.

### Automation budget

- `simp only [Except.ok.injEq]` with explicit lemma list
- `subst` for the injection equality
- `exact hf` to close the goal

No `ring`, `linarith`, `omega`, or broad `simp` needed.

### Helper lemmas needed

None — `Except.ok.injEq` is a standard Mathlib/Lean 4 simp lemma.

### What to watch for

`split_ifs` auto-closing the negative branch: the negative branch produces
`h : Except.error _ = Except.ok s` which Lean 4 resolves as a contradiction automatically.
Do NOT add a second focused bullet `·` for this branch — it will produce "No goals to be solved".

---

## SLICE-OL-05 — `radialTerm_eq` and `radial_denominator_nonzero_zero_coeffs`

### `radialTerm_eq`

**Goal shape:** Definitional equality — `radialTerm k r h = <expression>`.

**Classification:** Definitional equality.

**Opening move:** `rfl` — `radialTerm` is defined as exactly that expression. Lean's kernel will accept the proof term directly.

**Hard step:** None.

**Automation budget:** One tactic: `rfl`.

---

### `radial_denominator_nonzero_zero_coeffs`

**Goal shape:** `denominatorNonzero k r` where `denominatorNonzero k r` unfolds to `1 + k.k2 * r^2 + k.k4 * r^4 + k.k6 * r^6 ≠ 0`.

**Classification:** Negation (`≠`) — needs to reduce to `1 ≠ 0` after substituting zero coefficients.

**Opening move:** `simp [denominatorNonzero, hk2, hk4, hk6]` — unfolds the predicate, substitutes k2=k4=k6=0, simplifies `0 * r^n = 0`, `x + 0 = x`, leaving `1 ≠ 0`, which `simp` closes via `one_ne_zero`.

**Why it fits:** The goal is a compound of ring simplification and a literal inequality. `simp` with the explicit lemma list handles exactly this pattern.

**Fallback if `simp` leaves residual:** 
```lean
  unfold denominatorNonzero
  rw [hk2, hk4, hk6]
  norm_num
```
`norm_num` closes `1 + 0 * r^2 + 0 * r^4 + 0 * r^6 ≠ 0` directly.

**Hard step:** None.

**Automation budget:** One `simp` call with explicit list, or `unfold` + `rw` + `norm_num` if simp fails.

---

## SLICE-OL-06 — `radial_zero_coefficients_identity`

### Goal shape

`radialTerm k r h = 1`

Classification: **equality** — between a noncomputable real division expression and 1.

### Opening move

`simp only [radialTerm_eq, hk1, hk2, hk3, hk4, hk5, hk6, mul_zero, add_zero]`

This rewrites `radialTerm k r h` to its fraction form (via `radialTerm_eq`), substitutes all six zero hypotheses, then applies the arithmetic simp lemmas `mul_zero` and `add_zero` to reduce both numerator and denominator to `1`. The residual goal is `(1 : ℝ) / 1 = 1`.

### Closing the residual

`norm_num` closes `(1 : ℝ) / 1 = 1`.

### Full proof sketch

```lean
  simp only [radialTerm_eq, hk1, hk2, hk3, hk4, hk5, hk6, mul_zero, add_zero]
  norm_num
```

### Fallback if simp leaves `zero_mul` residuals

If `mul_zero` alone does not close `0 * r^n`, also add `zero_mul` to the simp set.
Alternatively, `ring_nf` after the substitutions normalizes polynomial arithmetic.

### Why no `field_simp` here

`field_simp` would require a nonzero denominator side condition. Since we are not dividing at the goal level after simplification (the denominator reduces to 1 which simp handles), `field_simp` is unnecessary.

### Hard step

None. The proof is pure arithmetic simplification after rewriting with the definition.
