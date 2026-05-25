---
name: radial-monotonicity-proof-capsule
description: Proof capsule for radialScale·r strict monotonicity and hScaleInj discharge
metadata:
  type: reference
---

# Proof Capsule — Radial Term Monotonicity

**Task slug:** `radial-monotonicity`
**Date started:** 2026-05-25
**Repo commit at start:** `a56f8eb67c2de4f3bb27acbd10fb08c5d88ebd5a`
**Model:** claude-sonnet-4-6
**Command:** `laps-start`
**Parent campaigns:** undistort-invertibility (hScaleInj first appeared in UI-01),
  nonconstructive-left-inverse (hScaleInj also appears in NCL-01)

---

## Goal

Prove that `fun r => radialScale k r * r` is strictly monotone on `{r : ℝ | 0 ≤ r}` under
the sign-separation coefficient constraint. Use this to derive a corollary that discharges
`hScaleInj` in `undistortPoint_injective_pure_radial` (UI-01) and
`undistortSub_nonconstructive_left_inverse_pure_radial` (NCL-01), upgrading both to
fully closed theorems (no open hypotheses beyond the new sign-constraint preconditions
and `hdenPos`).

---

## Design Decision (authorized 2026-05-25)

**Coefficient constraint:** k1,k3,k5 ≥ 0 AND k2,k4,k6 ≤ 0 (sign separation).

**Why this works globally (no r_max needed):**

Let `f(r) = radialScale k r * r = N(r)·r / D(r)` where `N(r) = 1 + k1r² + k3r⁴ + k5r⁶`
and `D(r) = 1 + k2r² + k4r⁴ + k6r⁶`. Writing the derivative numerator (with `s = r²`):

  g(s) = D(s)·(1 + 3k1s + 5k3s² + 7k5s³) − N(s)·(2k2s + 4k4s² + 6k6s³)

Under sign constraint:
- `2k2s + 4k4s² + 6k6s³ ≤ 0` for s ≥ 0 (since k2,k4,k6 ≤ 0)
- `N(s) ≥ 1 > 0` (since k1,k3,k5 ≥ 0)
- Therefore `−N(s)·(2k2s + ...) ≥ 0`
- `1 + 3k1s + ... ≥ 1` and `D(s) > 0` (by hdenPos), so first term ≥ D(s) > 0

Conclusion: `g(s) ≥ D(s) > 0`, so `f'(r) > 0` for all r ≥ 0 in the domain.

**Why not r_max:** A concrete sensor-radius bound alone does not imply monotonicity without
a coefficient condition. The sign constraint gives global closure and is checkable numerically
for any calibration. It covers lenses whose rational correction factor R(r) is non-decreasing
and the product R(r)·r is strictly increasing. This is documented as the theorem's scope.

---

## Theorem Statements (Proposed)

### Slice RM-00: Derivative positivity helper

```lean
-- Auxiliary: the derivative numerator is positive under sign constraint + hdenPos
-- Used internally in RM-01; may or may not be an independent theorem.
-- Key: 0 < (1 + 3*k1*r^2 + 5*k3*r^4 + 7*k5*r^6) * D(r) - N(r) * r * (2*k2*r + 4*k4*r^3 + 6*k6*r^5)
-- This follows from: first term ≥ D(r) > 0; second term ≤ 0.
```

### Slice RM-01: Strict monotonicity

```lean
theorem radialScale_mul_strictMono
    (k : RadialCoefficients)
    (hk1 : 0 ≤ k.k1) (hk3 : 0 ≤ k.k3) (hk5 : 0 ≤ k.k5)
    (hk2 : k.k2 ≤ 0) (hk4 : k.k4 ≤ 0) (hk6 : k.k6 ≤ 0)
    (hdenPos : ∀ r : ℝ, 0 ≤ r →
        0 < 1 + k.k2 * r ^ 2 + k.k4 * r ^ 4 + k.k6 * r ^ 6) :
    StrictMonoOn (fun r => radialScale k r * r) (Set.Ici 0)
```

### Slice RM-02: hScaleInj discharge

```lean
-- Corollary: discharges hScaleInj used in UI-01 and NCL-01
theorem radialScale_hScaleInj
    (k : RadialCoefficients)
    (hk1 : 0 ≤ k.k1) (hk3 : 0 ≤ k.k3) (hk5 : 0 ≤ k.k5)
    (hk2 : k.k2 ≤ 0) (hk4 : k.k4 ≤ 0) (hk6 : k.k6 ≤ 0)
    (hdenPos : ∀ r : ℝ, 0 ≤ r →
        0 < 1 + k.k2 * r ^ 2 + k.k4 * r ^ 4 + k.k6 * r ^ 6) :
    ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
        (radialScale k r₁) ^ 2 * r₁ ^ 2 = (radialScale k r₂) ^ 2 * r₂ ^ 2 → r₁ = r₂
```

---

## Key Proof Steps

**RM-00 (derivative computation + positivity):**
1. Define `numFun k r := r * (1 + k.k1 * r^2 + k.k3 * r^4 + k.k5 * r^6)` (i.e., r·N(r))
2. Define `denFun k r := 1 + k.k2 * r^2 + k.k4 * r^4 + k.k6 * r^6` (i.e., D(r))
3. Show `radialScale k r * r = numFun k r / denFun k r` (by `simp [radialScale, numFun, mul_div_assoc]`)
4. `HasDerivAt (numFun k) (1 + 3*k.k1*r^2 + 5*k.k3*r^4 + 7*k.k5*r^6) r`
   via `hasDerivAt_pow` + `HasDerivAt.const_mul` + `HasDerivAt.add`
5. `HasDerivAt (denFun k) (2*k.k2*r + 4*k.k4*r^3 + 6*k.k6*r^5) r` similarly
6. `HasDerivAt (numFun k / denFun k) derivVal r` via `HasDerivAt.div`
7. Show `derivVal > 0` via `nlinarith` / `positivity` using sign constraint + `hdenPos`

**RM-01 (strict monotonicity):**
Apply `strictMonoOn_of_deriv_pos` with:
- `D := Set.Ici 0` (domain)
- `hD := convex_Ici 0` 
- `hf`: ContinuousOn from `ContinuousOn.div` + polynomial continuity + hdenPos
- `hf'`: from RM-00, `deriv f r > 0` for `r ∈ Set.Ioi 0` (interior of Set.Ici 0)

**RM-02 (hScaleInj discharge):**
1. `(radialScale k r)^2 * r^2 = (radialScale k r * r)^2` — by `ring`
2. Both `radialScale k r₁ * r₁` and `radialScale k r₂ * r₂` are ≥ 0 (r ≥ 0, radialScale > 0)
3. `a^2 = b^2 ∧ 0 ≤ a ∧ 0 ≤ b → a = b` via `sq_left_inj` or `pow_left_injective`
4. From `f(r₁) = f(r₂)` and `StrictMonoOn.injOn`, conclude `r₁ = r₂`

---

## Load-Bearing Definitions

| Definition | Role | Status |
|---|---|---|
| `radialScale k r` | R(r) without proof arg; defined in InjectivityModel.lean (UI-01) | existing, not modified |
| `denominatorNonzero k r` | D(r) ≠ 0 predicate (RadialPolynomial.lean) | existing, not modified |
| `hdenPos` | New hypothesis: D(r) > 0 for all r ≥ 0; strictly stronger than denominatorNonzero | new in theorem statement |

Note: `hdenPos` is strictly stronger than `∀ r ≥ 0, denominatorNonzero k r` because it asserts
positivity (not just nonzero). Under k2,k4,k6 ≤ 0 + continuity + D(0)=1>0, nonzero implies
positive by IVT — but we take the direct positive formulation to avoid IVT machinery in the proof.

---

## Allowed Changes

- New theorems and their local `have`s
- `numFun` and `denFun` as local `let` or `def` (not part of project API — proof-internal only)
- Use of `HasDerivAt.*`, `strictMonoOn_of_deriv_pos`, `StrictMonoOn.injOn`, `Set.mem_Ici`
- `nlinarith`, `positivity`, `ring`, `linarith` for arithmetic closes

## Forbidden Changes

- No modification of `radialScale`, `denominatorNonzero`, `radialTerm`, or any prior theorem
- No `sorry`, `admit`, unauthorized `axiom`, `unsafe`, `partial`
- No weakening of the sign-separation constraint
- `numFun` and `denFun` must NOT be exported as API definitions (proof-internal only)

---

## File

`openlensio_semantics/InjectivityModel.lean` — append after NCL-01 section.
The monotonicity result is the direct discharge of hScaleInj from the same file's
existing injectivity theorems.
