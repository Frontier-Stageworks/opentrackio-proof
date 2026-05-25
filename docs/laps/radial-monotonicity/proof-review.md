---
name: radial-monotonicity-proof-review
description: Proof review for the radial-monotonicity campaign (RM-00 through RM-02)
metadata:
  type: reference
---

# Proof Review — Radial Term Monotonicity

**Task slug:** `radial-monotonicity`
**Review date:** 2026-05-25
**Reviewer:** claude-sonnet-4-6
**Repo state:** working tree (uncommitted; base commit `a56f8eb67c2de4f3bb27acbd10fb08c5d88ebd5a`)

---

## Declarations Added

| Declaration | Kind | File | Lines (approx.) |
|---|---|---|---|
| `radialScale_mul_derivPos` | private lemma | InjectivityModel.lean | ~55 |
| `radialScale_mul_strictMono` | theorem | InjectivityModel.lean | ~15 |
| `radialScale_hScaleInj` | theorem | InjectivityModel.lean | ~20 |

---

## Theorem Statement Audit

### `radialScale_mul_strictMono`

Statement matches intent (see statement-audit.md, verdict PASS):
- Domain: `Set.Ici 0` = [0, ∞) — correct
- Conclusion: `StrictMonoOn (fun r => radialScale k r * r) (Set.Ici 0)` — the direct monotonicity property needed
- Hypotheses: 6 sign constraints + hdenPos — minimal sufficient conditions established during campaign design

No vacuity: k = {0,…,0} satisfies all hypotheses; D(r) = 1 > 0; f(r) = r; strictly increasing. ✓

### `radialScale_hScaleInj`

Conclusion matches `hScaleInj` in UI-01 and NCL-01 exactly:
```lean
∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
    (radialScale k r₁) ^ 2 * r₁ ^ 2 = (radialScale k r₂) ^ 2 * r₂ ^ 2 → r₁ = r₂
```
Direct plug-in confirmed. ✓

---

## Proof Strategy Audit

### RM-00 (`radialScale_mul_derivPos`)

Proof:
1. Local `let numFun := fun r => r + k.k1*r^3 + k.k3*r^5 + k.k5*r^7`
2. Local `let denFun := fun r => 1 + k.k2*r^2 + k.k4*r^4 + k.k6*r^6`
3. `hfEq : radialScale k r * r = numFun r / denFun r` — by `ring`
4. `HasDerivAt numFun Nd r` — by chaining `hasDerivAt_id`, `hasDerivAt_pow`, `.const_mul`, `.add`
5. `HasDerivAt denFun Dd r` — by same pattern + `hasDerivAt_const` + `convert + ring` (normalizes leading 0)
6. `HasDerivAt (numFun / denFun) ((Nd*D - N*Dd)/D^2) r` — by `HasDerivAt.div`
7. `rw [hEqFun, h_quot.deriv]` — rewrites goal to the quotient-rule value
8. `div_pos`: numerator via `nlinarith` with sign facts; denominator via `pow_pos`

Sign argument (key):
- `Nd ≥ 1` because k1,k3,k5 ≥ 0 and all power terms ≥ 0
- `denFun r > 0` by hdenPos
- So `Nd * denFun r ≥ denFun r > 0`
- `numFun r ≥ 0` because r ≥ 0 and k1,k3,k5 ≥ 0
- `Dd ≤ 0` because k2,k4,k6 ≤ 0 and r ≥ 0
- So `numFun r * Dd ≤ 0`, i.e., `- numFun r * Dd ≥ 0`
- Total numerator ≥ denFun r > 0 ✓

No broad automation hiding the hard step: `nlinarith` is called with explicit auxiliary `have`s that expose the sign structure. ✓

### RM-01 (`radialScale_mul_strictMono`)

```lean
strictMonoOn_of_deriv_pos (convex_Ici 0)
```
- `ContinuousOn`: `ContinuousOn.mul + ContinuousOn.div + fun_prop` — polynomial numerator/denominator continuous; denominator nonzero from hdenPos via `ne_of_gt`
- Derivative positivity: `interior_Ici` gives `interior (Set.Ici 0) = Set.Ioi 0`; then delegates to `radialScale_mul_derivPos`

### RM-02 (`radialScale_hScaleInj`)

Chain:
1. `ring_nf; linarith` rewrites `(R·r)^2 = R^2·r^2` form to `(R·r)^2 = (R·r)^2`
2. `div_pos + nlinarith` establishes `0 < radialScale k rᵢ` (numerator ≥ 1 > 0, denominator > 0)
3. `mul_nonneg` gives `0 ≤ radialScale k rᵢ * rᵢ`
4. `pow_left_inj₀` (squaring injectivity on non-negatives) gives `f(r₁) = f(r₂)`
5. `StrictMonoOn.injOn` gives `r₁ = r₂`

Each step is justified by the relevant Mathlib lemma. No gaps. ✓

---

## Semantic Risk Check

| Risk | Assessment |
|---|---|
| Vacuity | No — k={0,…,0} satisfies all hypotheses; proof is non-trivial |
| Proxy property | No — StrictMonoOn and the hScaleInj conclusion are the intended properties |
| Definition drift | No — radialScale is unchanged; hdenPos is a new hypothesis (stronger than denominatorNonzero, documented) |
| Sorry / axiom | None — grep confirms (see verification below) |
| Weakened claim | No — StrictMonoOn (not MonoOn); injectivity on full [0,∞) |

---

## Verification Evidence

**Per-file check:**
```sh
lake env lean openlensio_semantics/InjectivityModel.lean
# exit 0, no output
```

**Full build:**
```sh
lake build InjectivityModel
# ✔ [3289/3290] Built InjectivityModel (4.1s)
# Build completed successfully (3290 jobs) — exit 0
```

**Sorry/axiom grep:**
```sh
grep -n "sorry\|admit\|#check\|unsafe\|partial" openlensio_semantics/InjectivityModel.lean
# no output
```

---

## Final Classification

- **Semantic proof action:** none
- **Verification/build action:** none (build confirmed exit 0)
- **Process evidence action:** none

**Verdict: Accepted**
