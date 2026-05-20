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

## SLICE-OL-05 — `radial_denominator_nonzero_zero_coeffs`

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

`simp only [radialTerm, hk1, hk2, hk3, hk4, hk5, hk6]`

Unfolds `radialTerm` directly and substitutes all six zero hypotheses. Both numerator and denominator reduce to `1`. The residual goal is `(1 : ℝ) / 1 = 1`.

### Closing the residual

`norm_num` closes `(1 : ℝ) / 1 = 1`.

### Full proof sketch

```lean
  simp only [radialTerm, hk1, hk2, hk3, hk4, hk5, hk6]
  norm_num
```

### Hard step

None. The proof is pure arithmetic simplification after unfolding the definition.

---

## SLICE-OL-08 — `tangential_zero_coefficients_identity` and `brown_conrady_zero_identity`

### `tangential_zero_coefficients_identity`

**Goal shape:** `undistortX k p ε h = radialTerm k (sensorRadius ε) h * ε.x`

**Classification:** Equality — polynomial simplification after substituting p1=p2=0.

**Opening move:** `simp only [undistortX, hp1, hp2, mul_zero, zero_mul, add_zero]`

Unfolds `undistortX`, substitutes zeros, and reduces:
- `2 * 0 * ε.x * ε.y → 0`
- `0 * (r^2 + 2 * ε.x^2) → 0`
- `radialTerm k r h * ε.x + 0 + 0 → radialTerm k r h * ε.x`

**Hard step:** None.

---

### `brown_conrady_zero_identity`

**Goal shape:** `undistortPoint k p ε h = ε`

**Classification:** Structural equality of `SensorPoint` values.

**Proof structure:** Three `have` steps, then close with `SensorPoint.ext`.

**Step 1 — R = 1:**
```lean
have hR : radialTerm k (sensorRadius ε) h = 1 :=
  radial_zero_coefficients_identity k (sensorRadius ε) hk1 hk2 hk3 hk4 hk5 hk6 h
```
Calls `radial_zero_coefficients_identity` (OL-06) explicitly. This confirms that lemma earns its place.

**Step 2 — X component:**
```lean
have hX : undistortX k p ε h = ε.x := by
  have htang := tangential_zero_coefficients_identity k p ε h hp1 hp2
  rw [htang, hR, one_mul]
```
Calls `tangential_zero_coefficients_identity` (this slice), then rewrites R to 1, then closes with `one_mul`.

**Step 3 — Y component (inline, no named lemma):**
```lean
have hY : undistortY k p ε h = ε.y := by
  simp only [undistortY, hp1, hp2, hR, mul_zero, zero_mul, add_zero, one_mul]
```
Y is handled inline — symmetric to X, but no named stepping-stone lemma was planned for it.

**Step 4 — Conclude:**
```lean
exact SensorPoint.ext hX hY
```
`SensorPoint.ext : s.x = t.x → s.y = t.y → s = t`. Since `undistortPoint` is definitionally `⟨undistortX ..., undistortY ...⟩`, `hX` and `hY` serve as proofs of the field equalities.

**Hard step:** None — structure equality follows from field equalities; field equalities follow from arithmetic simplification.

**Potential issue:** `SensorPoint.ext` expects `(undistortPoint k p ε h).x = ε.x` but `hX` has type `undistortX k p ε h = ε.x`. These are definitionally equal so Lean's kernel accepts this, but if not, use `show` to coerce or unfold `undistortPoint` first.

---

## SLICE-OL-09 — `deltaP_characterisation`, `deltaC_characterisation`, `distortion_center_translation_commutes`

All three theorems are component-level arithmetic closed by `ring` after unfolding definitions and splitting into x and y goals via `ext`.

### Common proof shape

```lean
ext <;> simp [addSensorPoints, subSensorPoints] <;> ring
```

- `ext` splits the `SensorPoint` equality into two `ℝ` equalities (`.x` and `.y`).
- `simp [addSensorPoints, subSensorPoints]` unfolds the definitions, exposing the raw arithmetic.
- `ring` closes each component goal.

### `deltaP_characterisation`

Goal after `ext`, x-component: `(ε'_u.x + ΔP.x) - ΔP.x = ε'_u.x`  
Closed by `ring` (`a + b - b = a`).

### `deltaC_characterisation`

Identical structure. Same proof.

### `distortion_center_translation_commutes`

Goal after `ext`, x-component: `((ε'_d.x + ΔP.x) - ΔC.x) - ΔP.x = ε'_d.x - ΔC.x`  
After ring normalization: `ε'_d.x + ΔP.x - ΔC.x - ΔP.x = ε'_d.x - ΔC.x` → `ε'_d.x - ΔC.x = ε'_d.x - ΔC.x` ✓  
Closed by `ring`.

### Hard step

None. All goals are linear arithmetic after unfolding.

### AMB-OL-002 test

If `addSensorPoints` used subtraction instead of addition, `deltaP_characterisation` would require `(ε'_u.x - ΔP.x) - ΔP.x = ε'_u.x` → `ε'_u.x - 2·ΔP.x = ε'_u.x` — false unless ΔP=0. The proof failing with wrong-sign definitions confirms the sign is meaningful.
