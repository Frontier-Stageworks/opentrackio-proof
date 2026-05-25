---
name: radial-monotonicity-statement-audit
description: Statement audit for radialScale_mul_strictMono (RM-01) and radialScale_hScaleInj (RM-02)
metadata:
  type: reference
---

# Statement Audit — Radial Term Monotonicity

**Task slug:** `radial-monotonicity`
**Audit date:** 2026-05-25

---

## RM-01: `radialScale_mul_strictMono`

### Intended claim

Under the sign-separation coefficient constraint (k1,k3,k5 ≥ 0, k2,k4,k6 ≤ 0) and with
the denominator positive on [0,∞), the function r ↦ R(r)·r is strictly increasing on [0,∞).

### Formal statement

```lean
theorem radialScale_mul_strictMono
    (k : RadialCoefficients)
    (hk1 : 0 ≤ k.k1) (hk3 : 0 ≤ k.k3) (hk5 : 0 ≤ k.k5)
    (hk2 : k.k2 ≤ 0) (hk4 : k.k4 ≤ 0) (hk6 : k.k6 ≤ 0)
    (hdenPos : ∀ r : ℝ, 0 ≤ r →
        0 < 1 + k.k2 * r ^ 2 + k.k4 * r ^ 4 + k.k6 * r ^ 6) :
    StrictMonoOn (fun r => radialScale k r * r) (Set.Ici 0)
```

### Statement-intent alignment

`StrictMonoOn f (Set.Ici 0)` is exactly "f is strictly increasing on [0,∞)" — the standard
Mathlib formulation. The hypotheses are:

- `hk1,hk3,hk5`: numerator coefficients non-negative. Required: under sign constraint,
  `1 + 3k1r² + 5k3r⁴ + 7k5r⁶ ≥ 1 > 0`, which makes the derivative numerator positive.
- `hk2,hk4,hk6`: denominator coefficients non-positive. Required: makes the second term
  of the derivative numerator ≤ 0, so the numerator is bounded below by D(r) > 0.
- `hdenPos`: D(r) > 0 for r ≥ 0. Required: without positivity (not just nonzero), the
  derivative formula involves division by D(r)², and D(r) > 0 ensures the quotient is
  positive. Also needed for ContinuousOn (no poles in the domain).

### Semantic risks

| Risk | Assessment |
|---|---|
| Vacuity | No. Hypothesis set is satisfiable: k = {0,0,0,0,0,0} gives R(r)=1, f(r)=r, strictly increasing. hdenPos holds: D(r)=1>0 always. |
| Weakened claim | No. StrictMonoOn (not MonoOn) on the full set [0,∞). |
| Over-strong hypotheses | hdenPos is necessary: without D(r)>0, f may not be monotone. Sign constraint is the minimal identified sufficient condition for derivative positivity. |
| Statement laundering | No. The proof will directly compute the derivative and apply strictMonoOn_of_deriv_pos; the monotonicity is the actual content. |
| Proxy property | No. StrictMonoOn is not a proxy — it IS the monotonicity property needed. |

### Verdict: PASS

---

## RM-02: `radialScale_hScaleInj`

### Intended claim

The sign-constraint conditions (+ hdenPos) discharge the `hScaleInj` hypothesis
carried by UI-01 and NCL-01, giving: for r₁,r₂ ≥ 0, if (R(r₁)·r₁)² = (R(r₂)·r₂)²
then r₁ = r₂.

### Formal statement

```lean
theorem radialScale_hScaleInj
    (k : RadialCoefficients)
    (hk1 : 0 ≤ k.k1) (hk3 : 0 ≤ k.k3) (hk5 : 0 ≤ k.k5)
    (hk2 : k.k2 ≤ 0) (hk4 : k.k4 ≤ 0) (hk6 : k.k6 ≤ 0)
    (hdenPos : ∀ r : ℝ, 0 ≤ r →
        0 < 1 + k.k2 * r ^ 2 + k.k4 * r ^ 4 + k.k6 * r ^ 6) :
    ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
        (radialScale k r₁) ^ 2 * r₁ ^ 2 = (radialScale k r₂) ^ 2 * r₂ ^ 2 → r₁ = r₂
```

### Statement-intent alignment

The conclusion exactly matches the `hScaleInj` hypothesis in UI-01:
```lean
-- From undistortPoint_injective_pure_radial:
hScaleInj : ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
    (radialScale k r₁) ^ 2 * r₁ ^ 2 = (radialScale k r₂) ^ 2 * r₂ ^ 2 → r₁ = r₂
```

`radialScale_hScaleInj k hk1 hk3 hk5 hk2 hk4 hk6 hdenPos` is a term of exactly
this type, providing a direct plug-in. The squared form `(R·r)² = (R·r)²` reduces to
`R·r = R·r` because both sides are ≥ 0 (r ≥ 0 and R(r) > 0 under hdenPos + sign constraint),
and squaring is injective on non-negatives. Then strict monotonicity closes r₁ = r₂.

### Semantic risks

| Risk | Assessment |
|---|---|
| Vacuity | No. Same satisfiable instance as RM-01. |
| Proxy property | No. The conclusion is exactly hScaleInj; no intermediate proxy. |
| Missing non-negativity of R(r) | Needed: radialScale k r > 0 for r ≥ 0. Under sign constraint, N(r) ≥ 1 > 0 and D(r) > 0 (hdenPos), so R = N/D > 0. This is a real sub-lemma needed in the proof. |
| Squared form vs. unquared form | The identity (R·r)² = R²·r² is `ring`. The step from (f r₁)² = (f r₂)² and 0 ≤ f rᵢ to f r₁ = f r₂ requires `sq_left_inj` or `pow_left_injective` — documented as a proof detail. |

### Verdict: PASS (with note: non-negativity of radialScale k r needed as sub-step)

---

## Hypothesis comparison: new theorems vs. UI-01/NCL

| UI-01 hypothesis | RM discharge condition |
|---|---|
| `hp1 : p.p1 = 0` | same (carried by caller) |
| `hp2 : p.p2 = 0` | same (carried by caller) |
| `hR₁ : radialTerm k (sensorRadius ε₁) h₁ ≠ 0` | same (carried by caller via hR_all in NCL) |
| `hScaleInj` | replaced by: 6 sign constraints + hdenPos |

The new hypotheses are more specific (sign constraint) but also more dischargeable: they are
checkable for any concrete calibration by evaluating the polynomial. No open mathematical
item remains once these are supplied.
