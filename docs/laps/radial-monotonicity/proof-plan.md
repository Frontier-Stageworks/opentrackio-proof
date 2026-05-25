---
name: radial-monotonicity-proof-plan
description: Proof plan for RM-00 (derivative positivity), RM-01 (StrictMonoOn), RM-02 (hScaleInj discharge)
metadata:
  type: reference
---

# Proof Plan — Radial Term Monotonicity

**Task slug:** `radial-monotonicity`
**Date:** 2026-05-25

---

## Proof Engineering Level

- **RM-00:** proving a fixed theorem (HasDerivAt computation + algebraic positivity)
- **RM-01:** proving a fixed theorem (StrictMonoOn from RM-00 via Mathlib)
- **RM-02:** proving a fixed theorem (corollary: squaring + injectivity)

---

## Slice RM-00: Derivative of radialScale·r and its positivity

### Goal

Establish `HasDerivAt (fun r => radialScale k r * r) d r` where `d > 0`, for all `r > 0`
under the sign-separation constraint and `hdenPos`.

### File

`openlensio_semantics/InjectivityModel.lean` — append.

### Key rewrite

`radialScale k r * r = (1 + k.k1 * r^2 + k.k3 * r^4 + k.k5 * r^6) / (1 + k.k2 * r^2 + k.k4 * r^4 + k.k6 * r^6) * r`

By `div_mul_eq_mul_div` or `mul_div_assoc`:
`= (r + k.k1 * r^3 + k.k3 * r^5 + k.k5 * r^7) / (1 + k.k2 * r^2 + k.k4 * r^4 + k.k6 * r^6)`

So locally define (inside the proof):
```
numFun r := r + k.k1 * r^3 + k.k3 * r^5 + k.k5 * r^7
denFun r := 1 + k.k2 * r^2 + k.k4 * r^4 + k.k6 * r^6
```

### HasDerivAt for numFun

`numFun_deriv r = 1 + 3 * k.k1 * r^2 + 5 * k.k3 * r^4 + 7 * k.k5 * r^6`

Proof assembly:
```lean
have h_id : HasDerivAt (fun r => r) 1 r := hasDerivAt_id r
have h_r3 : HasDerivAt (fun r => r^3) (3 * r^2) r := by
  have := hasDerivAt_pow 3 r; simp [Nat.cast_ofNat] at this ⊢; linarith
have h_k1r3 : HasDerivAt (fun r => k.k1 * r^3) (k.k1 * (3 * r^2)) r :=
  h_r3.const_mul k.k1
-- ... similarly for r^5, r^7
-- Sum via HasDerivAt.add, prove derivative = numFun_deriv via ring
```

### HasDerivAt for denFun

`denFun_deriv r = 2 * k.k2 * r + 4 * k.k4 * r^3 + 6 * k.k6 * r^5`

Assembled similarly from `hasDerivAt_pow 2`, `hasDerivAt_pow 4`, `hasDerivAt_pow 6`,
`HasDerivAt.const_mul`, `HasDerivAt.add`, `hasDerivAt_const`.

### HasDerivAt for numFun / denFun

```lean
have hd : denFun r ≠ 0 := ne_of_gt (hdenPos r hr)
exact (h_numFun.div h_denFun hd)
-- Result: HasDerivAt (numFun / denFun) ((numFun_deriv * denFun r - numFun r * denFun_deriv) / denFun r^2) r
```

Note: `HasDerivAt.div` gives `(c' * d x - c x * d') / d x^2` (confirmed from Mathlib source).

### Derivative positivity

The numerator of the derivative is:
`N = (1 + 3k1r² + 5k3r⁴ + 7k5r⁶) * D(r) - (r + k1r³ + k3r⁵ + k5r⁷) * (2k2r + 4k4r³ + 6k6r⁵)`
`= (1 + 3k1r² + 5k3r⁴ + 7k5r⁶) * D(r) - numFun r * denFun_deriv`

Under sign constraint (all signs established from hypotheses):
- `term1 := (1 + 3*k.k1*r^2 + ...) * D(r)` — both factors ≥ 0, first ≥ 1, so term1 ≥ D(r) > 0
- `numFun r ≥ 0` for r ≥ 0 (all terms ≥ 0 since k.k1,k.k3,k.k5 ≥ 0)
- `denFun_deriv ≤ 0` for r ≥ 0 (since k.k2,k.k4,k.k6 ≤ 0 and r ≥ 0)
- So `numFun r * denFun_deriv ≤ 0`, hence `-numFun r * denFun_deriv ≥ 0`
- Total: N ≥ D(r) > 0

**Hard step:** `nlinarith` with the above facts as local `have`s:
```lean
have h1 : 0 < D := hdenPos r hr
have h2 : 0 ≤ 1 + 3 * k.k1 * r^2 + 5 * k.k3 * r^4 + 7 * k.k5 * r^6 := by positivity
have h3 : 0 ≤ numFun r := by ... (positivity or nlinarith from r ≥ 0, k signs)
have h4 : denFun_deriv ≤ 0 := by nlinarith [sq_nonneg r, ...]
-- Conclude: N > 0
nlinarith [mul_nonneg h2 (le_of_lt h1), mul_nonpos_of_nonneg_of_nonpos h3 h4]
```

The denominator `denFun r^2 > 0` from `sq_pos_of_ne_zero` + `ne_of_gt h1`.
Therefore `HasDerivAt value > 0`. ✓

### Interface to `deriv`

`strictMonoOn_of_deriv_pos` needs `0 < deriv f x`. Use:
```lean
have hDeriv := h_f.deriv  -- HasDerivAt.deriv : HasDerivAt f d x → deriv f x = d
rw [hDeriv]
exact h_d_pos  -- the HasDerivAt value is positive
```

---

## Slice RM-01: StrictMonoOn

### Proof shape

```lean
apply strictMonoOn_of_deriv_pos (convex_Ici 0)
· -- ContinuousOn (fun r => radialScale k r * r) (Set.Ici 0)
  apply ContinuousOn.div
  · continuity  -- or explicit ContinuousOn for polynomial
  · continuity
  · intro r hr; exact ne_of_gt (hdenPos r hr)
· -- ∀ x ∈ interior (Set.Ici 0) = Set.Ioi 0, 0 < deriv f x
  intro r hr
  rw [interior_Ici] at hr  -- hr : 0 < r
  -- apply RM-00 at r with 0 < r (i.e., 0 ≤ r from le_of_lt hr)
```

**Risk:** `continuity` tactic might not handle `radialScale k r * r` automatically since
`radialScale` uses real division and the denominator nonzero condition is not globally
encoded. Alternative: `ContinuousOn.div` with explicit continuity of numerator and
denominator + `ne_of_gt (hdenPos r hr)`.

---

## Slice RM-02: hScaleInj discharge

### Proof shape

```lean
intro r₁ r₂ hr₁ hr₂ h
-- h : (radialScale k r₁)^2 * r₁^2 = (radialScale k r₂)^2 * r₂^2
-- Rewrite: (R·r)^2 = R^2·r^2
have hEq : (radialScale k r₁ * r₁)^2 = (radialScale k r₂ * r₂)^2 := by ring_nf; linarith
-- Both sides ≥ 0
have hf1 : 0 ≤ radialScale k r₁ * r₁ := mul_nonneg (le_of_lt (radialScale_pos r₁ hr₁)) hr₁
have hf2 : 0 ≤ radialScale k r₂ * r₂ := mul_nonneg (le_of_lt (radialScale_pos r₂ hr₂)) hr₂
-- sq_left_inj / pow_left_injective
have hfEq : radialScale k r₁ * r₁ = radialScale k r₂ * r₂ := by
  exact ... -- sq_left_inj or similar
-- Apply StrictMonoOn.injOn
exact (radialScale_mul_strictMono k ...).injOn hr₁ hr₂ hfEq
```

Where `radialScale_pos r hr : 0 < radialScale k r` is a helper: since N(r) ≥ 1 > 0
and D(r) > 0 by hdenPos, R(r) = N(r)/D(r) > 0. This is a `have` inside the proof or
a helper lemma.

---

## Expected Hard Steps

| Step | Slice | Why hard |
|---|---|---|
| `HasDerivAt` assembly for `numFun` and `denFun` | RM-00 | Polynomial terms require chaining multiple `HasDerivAt` lemmas; `ring` cleanup for the derivative expression |
| Derivative numerator positivity | RM-00 | `nlinarith` with several auxiliary inequality facts; may need explicit intermediate `have`s to guide `nlinarith` |
| `ContinuousOn` for `radialScale k r * r` | RM-01 | `continuity` may not handle division with nonzero denominator automatically; may need `ContinuousOn.div` explicitly |
| Squaring injectivity on non-negatives (AMB-RM-003) | RM-02 | Exact Mathlib lemma name unknown; may need `Real.sqrt_inj` or `abs_eq_abs` detour |

---

## Non-Goals

- Discharging `hdenPos` itself (remains a caller obligation — dependent on coefficient magnitudes)
- Discharging `hR_all` in NCL (separate condition, not addressed here)
- General-p (tangential) injectivity (blocked by on-circle restriction of UI-03)

---

## Lean Check Requirements

- Per-slice: `lake env lean openlensio_semantics/InjectivityModel.lean`, exit 0
- After RM-02: `lake build`, exit 0, no warnings
