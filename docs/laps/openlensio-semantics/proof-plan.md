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

---

## SLICE-OL-10 — `projection_matrix_undistort_eq`

### Goal shape

```
subSensorPoints (subSensorPoints (undistortFromDistorted k p ε_d ΔC ΔP h) ΔC) ΔP =
undistortPoint k p (subSensorPoints (subSensorPoints ε_d ΔC) ΔP) h
```

Classification: **structural equality of `SensorPoint`** — after unfolding, reduces to two component arithmetic goals.

### Opening move

```lean
ext <;> simp [undistortFromDistorted, addSensorPoints, subSensorPoints] <;> ring
```

- `ext` splits into x- and y-component equalities.
- `simp [undistortFromDistorted, addSensorPoints, subSensorPoints]` unfolds the three definitions, exposing raw `ℝ` arithmetic.
- `ring` closes each component goal.

### Why it fits

`undistortFromDistorted k p ε_d ΔC ΔP h` unfolds to:
```
addSensorPoints (addSensorPoints (undistortPoint k p ε' h) ΔC) ΔP
```
where `ε' = subSensorPoints (subSensorPoints ε_d ΔC) ΔP`.

After `simp`, the x-component goal is:
```
(undistortPoint k p ε' h).x + ΔC.x + ΔP.x - ΔC.x - ΔP.x = (undistortPoint k p ε' h).x
```

`ring` treats `(undistortPoint k p ε' h).x` as an opaque variable `a` and closes `a + b + c - b - c = a`.

### Expected hard step

None. The proof is pure linear arithmetic after unfolding. The same `ext <;> simp <;> ring` pattern succeeds in OL-09 for identical structural reasons.

### Definitions to unfold

| Definition | Where | Role |
|---|---|---|
| `undistortFromDistorted` | ProjectionModel.lean | Exposes the `+ΔC+ΔP` wrapping |
| `addSensorPoints` | DeltaSemantics.lean | Exposes component addition |
| `subSensorPoints` | DeltaSemantics.lean | Exposes component subtraction |

`undistortPoint` is NOT unfolded — it is treated as an opaque term by `ring`.

### Helper lemmas needed

None. The proof stands alone; it does not call any previous lemmas.

### Automation budget

Three tactics: `ext`, `simp [...]`, `ring`. The `simp` step is constrained to explicit definitions — no global simp set.

### Hard step identification

The theorem is not trivially true: if the order of `addSensorPoints` were `(undistortPoint + ΔP + ΔC)` instead of `(undistortPoint + ΔC + ΔP)`, then `subSensorPoints ... ΔC ΔP` would give `undistortPoint + ΔP - ΔP = undistortPoint` but the x-component arithmetic would differ by `ΔC.x - ΔC.x` vs `ΔP.x - ΔC.x` depending on order. The fact that the proof compiles confirms the definition order is consistent with the theorem statement.

---

## SLICE-OL-11 — `fov_undistort_eq`

### Goal shape

```
undistortFromDistorted k p (addSensorPoints ε'_d ΔP) ΔC ΔP coerced_h =
addSensorPoints (fovUndistortFromDistorted k p ε'_d ΔC h) ΔP
```

Classification: **structural equality of `SensorPoint`** — after unfolding and applying `distortion_center_translation_commutes`, reduces to `undistortPoint` calls with the same argument, closed by proof irrelevance.

### Hard step and resolution

`undistortFromDistorted` requires `h' : denominatorNonzero k (sensorRadius A_big)` (where `A_big` is the long subSensorPoints expression) while `fovUndistortFromDistorted` uses `h : denominatorNonzero k (sensorRadius A_small)`. These are propositionally equal via `distortion_center_translation_commutes` but NOT definitionally equal — `rfl` cannot bridge them directly.

**Resolution:** Two explicit hypotheses (`h` and `h'`) in the theorem statement, plus a private helper `undistortPoint_congr` that uses `subst hε; rfl` to bridge the equality. `subst` works because `ε₁` is a free variable in the helper's local context, allowing substitution.

**Plan deviation from Stop 2 draft:** The original plan proposed `(distortion_center_translation_commutes ...).symm ▸ h` in the theorem statement (single-hypothesis form). After a failed build attempt that revealed `addSensorPoints` unfolding breaks the simp pattern, and after analysis showing `▸` in term position risks elaboration issues, the two-hypothesis form was chosen as cleaner and verified correct.

### Opening move

```lean
simp only [undistortFromDistorted, fovUndistortFromDistorted]
```

Unfolds the two function definitions. `addSensorPoints` is NOT included — including it would unfold `addSensorPoints ε'_d ΔP` to a struct literal, breaking the pattern that `distortion_center_translation_commutes` matches.

### Closing move

```lean
congr 1; congr 1
exact undistortPoint_congr k p (distortion_center_translation_commutes ε'_d ΔP ΔC) h' h
```

After `simp only`, the goal is:
```
addSensorPoints (addSensorPoints (undistortPoint k p A_big h') ΔC) ΔP =
addSensorPoints (addSensorPoints (undistortPoint k p A_small h) ΔC) ΔP
```

`congr 1; congr 1` strips the two `addSensorPoints` wrappers, leaving:
```
undistortPoint k p A_big h' = undistortPoint k p A_small h
```

`undistortPoint_congr k p (distortion_center_translation_commutes ε'_d ΔP ΔC) h' h` closes this using `A_big = A_small` and proof irrelevance.

### Why it fits

`undistortPoint_congr` has a clear, documented role: bridge the `undistortPoint` equality under propositional SensorPoint equality. `distortion_center_translation_commutes` (OL-09) provides the SensorPoint equality. `congr 1; congr 1` peels the structural wrapper.

### Expected hard step

The `congr 1; congr 1` decomposition — `congr 1` on `addSensorPoints X Y = addSensorPoints X' Y` produces `addSensorPoints X = addSensorPoints X'` (with `Y = Y` auto-closed by `rfl`), and one more `congr 1` gives the `undistortPoint` equality goal.

### Definitions to unfold

| Definition | Role |
|---|---|
| `undistortFromDistorted` | Exposes `U((ε'_d + ΔP) − ΔC − ΔP) + ΔC + ΔP` |
| `fovUndistortFromDistorted` | Exposes `U(ε'_d − ΔC) + ΔC` |
| `addSensorPoints` | Exposes component addition |
| `distortion_center_translation_commutes` | Rewrites the shifted argument |

`undistortPoint` is NOT unfolded — opaque; proof irrelevance closes the remaining equality.

### Helper lemmas used

`distortion_center_translation_commutes` (OL-09) — called in both coercion and simp set.

### Automation budget

Two: `simp only [...]`, `rfl`.

---

## SLICE-OL-12 — `angle_of_view_eq`

### Goal shape

`Real.tan (angleOfView F r_u / 2) = r_u / F`

Classification: **real function equality** — reduces to `Real.tan (Real.arctan x) = x` after unfolding.

### Opening move

```lean
unfold angleOfView
simp [Real.tan_arctan]
```

After `unfold angleOfView`, the LHS becomes `Real.tan (2 * Real.arctan (r_u / F) / 2)`. After arithmetic simplification `2 * x / 2 = x`, this becomes `Real.tan (Real.arctan (r_u / F))`. Then `Real.tan_arctan (r_u / F)` closes the goal.

`simp [Real.tan_arctan]` should handle the arithmetic simplification and the Mathlib identity in one step.

### Expected hard step

None. The theorem is a direct consequence of `Real.tan_arctan` after unfolding the definition.

### Mathlib lemma

`Real.tan_arctan : ∀ (x : ℝ), Real.tan (Real.arctan x) = x` — unconditional, no domain restriction.

### Automation budget

Two: `unfold angleOfView`, `simp [Real.tan_arctan]`. Or one: `simp [angleOfView, Real.tan_arctan]`.

---

## SLICE-OL-13 — `pixel_metric_roundtrip`, `image_texture_coordinate_roundtrip`

### Goal shape

Two `SensorPoint` equalities:

1. `fromShaderCoords w h wshader (toShaderCoords w h wshader p) = p`  
2. `toShaderCoords w h wshader (fromShaderCoords w h wshader q) = q`

Classification: **equality** — roundtrip of two component-wise affine functions over ℝ.

### Opening move

`ext` — splits the `SensorPoint` equality into two component goals (`x` component and `y` component).

### Why it fits

`toShaderCoords` and `fromShaderCoords` are defined component-wise as affine maps. After `ext`, each component goal is a rational-function identity over ℝ with `w`, `h`, `wshader` in denominators.

### Expected hard step

None. All three positivity hypotheses (`hw : 0 < w`, `hh : 0 < h`, `hs : 0 < wshader`) are needed to discharge division-by-zero side conditions.

- `hw.ne'` provides `w ≠ 0` for the `x` component of `fromShaderCoords`
- `hh.ne'` provides `h ≠ 0` for the `y` component of `fromShaderCoords`
- `hs.ne'` provides `wshader ≠ 0` for both components of `toShaderCoords`

### Proof script (both theorems)

```lean
theorem pixel_metric_roundtrip ... := by
  ext <;> simp [fromShaderCoords, toShaderCoords] <;>
  field_simp [hw.ne', hh.ne', hs.ne'] <;> ring

theorem image_texture_coordinate_roundtrip ... := by
  ext <;> simp [toShaderCoords, fromShaderCoords] <;>
  field_simp [hw.ne', hh.ne', hs.ne'] <;> ring
```

### Helper lemmas needed

None.

### Automation budget

Three tactics per theorem: `ext`, `simp [defs]`, `field_simp [ne'] + ring`. All mechanical.
