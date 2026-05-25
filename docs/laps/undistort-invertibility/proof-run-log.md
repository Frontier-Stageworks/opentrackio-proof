---
name: undistort-invertibility-proof-run-log
description: Proof run log for the undistort invertibility campaign — records Lean check results and tactic outcomes per slice
metadata:
  type: reference
---

# Proof Run Log — Undistort Invertibility Campaign

---

## SLICE-UI-00 — undistortPoint_injective_zero_tangential

**Date:** 2026-05-24

### Lean check

```
lake env lean openlensio_semantics/InjectivityModel.lean
```

**Result:** exit 0, no output, no warnings, no sorry warnings.

### Tactic trace

| Step | Tactic | Outcome |
|---|---|---|
| 1 | `have hRR : ... := by simp only [radialTerm, hSameR]` | Closed. `simp only [radialTerm]` unfolded the definition; `hSameR` equated sensorRadius arguments; `rfl` closed. |
| 2 | `have hR' := hRR ▸ hR` | Closed. Type-level rewrite transfers ≠ 0 condition from ε₁ to ε₂ term. |
| 3 | `have hX := congr_arg SensorPoint.x hU` | Closed. Definitional equality of `(undistortPoint ...).x` with `undistortX ...` accepted without annotation. |
| 4 | `have hY := congr_arg SensorPoint.y hU` | Closed. Same as above for y. |
| 5 | `simp only [undistortX, hp1, hp2, mul_zero, zero_mul, add_zero] at hX` | Closed. Tangential terms zeroed out. hX reduced to `R₁ * ε₁.x = R₂ * ε₂.x`. |
| 6 | `simp only [undistortY, hp1, hp2, mul_zero, zero_mul, add_zero] at hY` | Closed. hY reduced to `R₁ * ε₁.y = R₂ * ε₂.y`. |
| 7 | `rw [hRR] at hX hY` | Closed. LHS radial term rewritten to ε₂'s radial term on both hypotheses. |
| 8 | `exact SensorPoint.ext (mul_left_cancel₀ hR' hX) (mul_left_cancel₀ hR' hY)` | Closed. ε₁.x = ε₂.x and ε₁.y = ε₂.y via cancellation; SensorPoint.ext closes ε₁ = ε₂. |

### Failed attempts

None. Proof compiled on the first attempt, exactly following the proof plan.

### Placeholder hygiene check

- No `sorry` ✓
- No `admit` ✓
- No unauthorized `axiom` ✓
- No `unsafe` or `partial` ✓
- No `set_option warn.sorry false` ✓
- No Lean warnings present ✓

---

## SLICE-UI-01 — undistortPoint_injective_pure_radial

**Date:** 2026-05-24

### Lean check

```
lake env lean openlensio_semantics/InjectivityModel.lean
```

**Result:** exit 0, no output, no warnings, no sorry warnings.

### Tactic trace

| Step | Tactic | Outcome |
|---|---|---|
| 1 | `simp [radialTerm, radialScale]` in `radialTerm_eq_radialScale` | Closed. Both definitions unfold to the same rational expression; simp closes with rfl. |
| 2 | `have hX := congr_arg SensorPoint.x hU` | Closed. Definitional equality of `(undistortPoint ...).x` with `undistortX ...` accepted. |
| 3 | `have hY := congr_arg SensorPoint.y hU` | Closed. Same for y. |
| 4 | `simp only [undistortX, hp1, hp2, mul_zero, zero_mul, add_zero] at hX` | Closed. hX reduced to `R₁ * ε₁.x = R₂ * ε₂.x`. |
| 5 | `simp only [undistortY, hp1, hp2, mul_zero, zero_mul, add_zero] at hY` | Closed. hY reduced to `R₁ * ε₁.y = R₂ * ε₂.y`. |
| 6 | `have h := congr_arg (· ^ 2) hX; simp only [mul_pow] at h; exact h` for hX2 | Closed. Squaring hX and distributing gives `R₁² * ε₁.x² = R₂² * ε₂.x²`. |
| 7 | Same as step 6 for hY2 | Closed. `R₁² * ε₁.y² = R₂² * ε₂.y²`. |
| 8 | `unfold sensorRadius; rw [Real.sq_sqrt (by positivity)]` for hsr1 | Closed. `(√(ε₁.x²+ε₁.y²))² = ε₁.x²+ε₁.y²` via Real.sq_sqrt; positivity closes the nonnegativity side condition. |
| 9 | Same as step 8 for hsr2 | Closed. |
| 10 | `nlinarith [hX2, hY2]` for hSumXY | Closed. `R₁²*(x₁²+y₁²) = R₂²*(x₂²+y₂²)` follows by adding hX2 and hY2; nlinarith handles the ring expansion. |
| 11 | `rw [← radialTerm_eq_radialScale ..., ← radialTerm_eq_radialScale ..., hsr1, hsr2]; exact hSumXY` for hSum | Closed. Rewrites expose hSumXY as the goal after substitution. |
| 12 | `hScaleInj _ _ (sensorRadius_nonneg ε₁) (sensorRadius_nonneg ε₂) hSum` for hr | Closed. Caller-supplied injectivity applied to hSum yields `sensorRadius ε₁ = sensorRadius ε₂`. |
| 13 | `exact undistortPoint_injective_zero_tangential k p hp1 hp2 ε₁ ε₂ h₁ h₂ hR₁ hr hU` | Closed. UI-00 accepts the now-derived same-radius condition and closes ε₁ = ε₂. |

### Failed attempts

None. Proof compiled on the first attempt, exactly following the proof plan.

### Placeholder hygiene check

- No `sorry` ✓
- No `admit` ✓
- No unauthorized `axiom` ✓
- No `unsafe` or `partial` ✓
- No `set_option warn.sorry false` ✓
- No Lean warnings present ✓

---

## SLICE-UI-02 — radialTerm_pos / radialTerm_ne_zero

**Date:** 2026-05-24

### Lean check

```
lake env lean openlensio_semantics/InjectivityModel.lean
```

**Result:** exit 0, no output, no warnings.

### Tactic trace

| Step | Tactic | Outcome |
|---|---|---|
| 1 | `simp only [radialTerm]` in `radialTerm_pos` | Closed by unfolding. Goal becomes `0 < (num) / (den)`. |
| 2 | `exact div_pos hNum hDen` | Closed. Mathlib `div_pos` applies directly. |
| 3 | `(radialTerm_pos k r h hNum hDen).ne'` in `radialTerm_ne_zero` | Closed. `.ne'` derives `x ≠ 0` from `0 < x`. |

### Failed attempts

None. Both theorems compiled on the first attempt.

### Placeholder hygiene check

- No `sorry` ✓
- No `admit` ✓
- No unauthorized `axiom` ✓
- No `unsafe` or `partial` ✓
- No `set_option warn.sorry false` ✓
- No Lean warnings present ✓

---

## SLICE-UI-03 — undistortPoint_injective_on_circle_tangential

**Date:** 2026-05-24

### Lean check

```
lake env lean openlensio_semantics/InjectivityModel.lean
```

**Result:** exit 0, no output, no warnings.

### Tactic trace

| Step | Tactic | Outcome |
|---|---|---|
| 1 | `simp only [radialTerm, hSameR]` for hRR | Closed. Same mechanism as UI-00: h ignored in body, hSameR equates radii. |
| 2 | `congr_arg SensorPoint.x hU` for hX | Closed. |
| 3 | `congr_arg SensorPoint.y hU` for hY | Closed. |
| 4 | `simp only [undistortX] at hX` | Closed. Unfolds with tangential terms kept. |
| 5 | `simp only [undistortY] at hY` | Closed. Unfolds with tangential terms kept. |
| 6 | `rw [← hRR, ← hSameR] at hX hY` | Closed. Both hX and hY now have the same R and sensorRadius on both sides; sensorRadius ε₁ ^ 2 cancels in subsequent ring check. |
| 7 | `linear_combination D * hX - B * hY` for hδx | Closed. ring verified (AD−BC)·δx = D·(LHS_X−RHS_X) − B·(LHS_Y−RHS_Y) as a polynomial identity. sensorRadius ε₁ ^ 2 treated as opaque atom; cancels. |
| 8 | `linear_combination A * hY - C * hX` for hδy | Closed. ring verified (AD−BC)·δy = A·(LHS_Y−RHS_Y) − C·(LHS_X−RHS_X). |
| 9 | `rcases mul_eq_zero.mp hδx with h \| h` for hx | First case: `absurd h hDet` closed contradiction. Second case: `linarith` from ε₁.x − ε₂.x = 0. |
| 10 | Same pattern for hy | Closed. |
| 11 | `exact SensorPoint.ext hx hy` | Closed. |

### Failed attempts

None. Proof compiled on the first attempt, exactly following the proof plan.

### Placeholder hygiene check

- No `sorry` ✓
- No `admit` ✓
- No unauthorized `axiom` ✓
- No `unsafe` or `partial` ✓
- No `set_option warn.sorry false` ✓
- No Lean warnings present ✓

---

## SLICE-UI-04 — radialDescale / radialDescale_left_inverse_zero_tangential

**Date:** 2026-05-24

### Lean check

```
lake env lean openlensio_semantics/InjectivityModel.lean
```

**Result:** exit 0, no output, no warnings.

### Tactic trace

| Step | Tactic | Outcome |
|---|---|---|
| 1 | `simp only [radialDescale, undistortPoint, undistortX, undistortY, hp1, hp2, mul_zero, zero_mul, add_zero]` | Closed. All definitions unfolded; tangential terms zeroed; goal reduced to `⟨R * ε.x / R, R * ε.y / R⟩ = ε`. |
| 2 | `exact SensorPoint.ext (mul_div_cancel_left₀ ε.x hR) (mul_div_cancel_left₀ ε.y hR)` | Closed. `mul_div_cancel_left₀` applied to each component; `SensorPoint.ext` assembles. |

### Failed attempts

None. Compiled on first attempt. `mul_div_cancel_left₀` matched the exact post-simp form.

### Placeholder hygiene check

- No `sorry` ✓
- No `admit` ✓
- No unauthorized `axiom` ✓
- No `unsafe` or `partial` ✓
- No `set_option warn.sorry false` ✓
- No Lean warnings present ✓
