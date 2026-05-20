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
