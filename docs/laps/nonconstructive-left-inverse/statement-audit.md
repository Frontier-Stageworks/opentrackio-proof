---
name: nonconstructive-left-inverse-statement-audit
description: Statement audit for the nonconstructive left-inverse theorems (NCL-00 and NCL-01)
metadata:
  type: reference
---

# Statement Audit — Nonconstructive Left Inverse

**Task slug:** `nonconstructive-left-inverse`
**Audit date:** 2026-05-25
**Repo commit at start:** `494947f8f84032390c560148d87fe8ce2c115a87`

---

## Slice NCL-00: `undistortSub_injective_pure_radial`

### Intended claim

For the pure-radial Brown-Conrady map (p₁ = p₂ = 0), the wrapper function
`undistortSub k p : DomainPoint k → SensorPoint` is injective: if two domain points
map to the same output, they are the same domain point.

### Formal statement

```lean
theorem undistortSub_injective_pure_radial
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (hp1 : p.p1 = 0) (hp2 : p.p2 = 0)
    (hR_all : ∀ (ε : SensorPoint) (h : denominatorNonzero k (sensorRadius ε)),
        radialTerm k (sensorRadius ε) h ≠ 0)
    (hScaleInj : ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
        (radialScale k r₁) ^ 2 * r₁ ^ 2 = (radialScale k r₂) ^ 2 * r₂ ^ 2 → r₁ = r₂) :
    Function.Injective (undistortSub k p)
```

### Statement-intent alignment

The statement matches the intended claim. `Function.Injective (undistortSub k p)` is the
standard Mathlib formulation of injectivity for a plain function. The hypotheses are:

- `hp1`, `hp2`: pure-radial restriction. Honest — the on-circle tangential result (UI-03)
  does not give global injectivity; pure-radial (UI-01) does.
- `hR_all`: global lift of UI-01's per-point `hR₁ : radialTerm k (sensorRadius ε₁) h₁ ≠ 0`.
  For `Function.Injective`, we must cover all input pairs — so a global condition is
  required. This is the minimal sufficient lift.
- `hScaleInj`: carried from UI-01. Remains open per next-steps item 5. Honest hypothesis.

### Semantic risks

| Risk | Assessment |
|---|---|
| Vacuity | No. Both `DomainPoint k` and `SensorPoint` are inhabited for all k; the injectivity condition is genuinely non-trivial. |
| Proxy property | No. `Function.Injective` directly states the intended injectivity claim. |
| Weakened claim | No. The conclusion is exactly injectivity; no scope narrowing vs. UI-01. |
| Over-strong hypotheses | `hR_all` is the minimal global R ≠ 0 condition. `hScaleInj` is inherited from UI-01 and documented as open. Neither is overly restrictive. |
| Statement laundering | No. The proof will go: `intro ⟨ε₁,h₁⟩ ⟨ε₂,h₂⟩ hU; Subtype.ext; undistortPoint_injective_pure_radial`. The injectivity in the conclusion is exactly the content of UI-01, lifted to the subtype. |

### Verdict: PASS — statement matches intent; no semantic risk detected.

---

## Slice NCL-01: `undistortSub_nonconstructive_left_inverse_pure_radial`

### Intended claim

For the pure-radial case, the Mathlib-defined nonconstructive inverse function
`Function.invFun (undistortSub k p)` is a left inverse of `undistortSub k p`:
applying D then U then D gives D(U(ε)) = ε for every domain point ε.

### Formal statement

```lean
theorem undistortSub_nonconstructive_left_inverse_pure_radial
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (hp1 : p.p1 = 0) (hp2 : p.p2 = 0)
    (hR_all : ∀ (ε : SensorPoint) (h : denominatorNonzero k (sensorRadius ε)),
        radialTerm k (sensorRadius ε) h ≠ 0)
    (hScaleInj : ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
        (radialScale k r₁) ^ 2 * r₁ ^ 2 = (radialScale k r₂) ^ 2 * r₂ ^ 2 → r₁ = r₂)
    (εd : DomainPoint k) :
    Function.invFun (undistortSub k p) (undistortSub k p εd) = εd
```

### Statement-intent alignment

The statement matches the intended claim. `Function.invFun f (f a) = a` is exactly
"D ∘ U = id at every domain point a" where D = Function.invFun (undistortSub k p).

The relation to the spec (OpenLensIO Eqs 5, 11: D = U⁻¹):
- The spec asserts D exists as a mathematical object. This theorem proves it exists
  (via `Classical.choice`) and satisfies the defining property D(U(ε)) = ε.
- No closed-form formula is asserted or needed. The nonconstructive character is
  explicit in the use of `Function.invFun`.

### Comparison with UI-04 (`radialDescale_left_inverse_zero_tangential`)

| Property | UI-04 (`radialDescale`) | NCL-01 (`Function.invFun`) |
|---|---|---|
| Explicit formula | Yes: `⟨ε.x/R(r), ε.y/R(r)⟩` | No — Classical.choice |
| Extra input required | Yes: explicit `r` (input radius) | No — output suffices |
| Restricted to p = 0 | Yes | Yes |
| Proves D(U(ε)) = ε | Yes | Yes |
| Proof of U(D(u)) = u | No | No (left inverse only) |

The NCL-01 theorem is strictly stronger than UI-04 in the "no extra input" sense:
the nonconstructive D requires only the output, not the input radius. But it is
weaker in the "explicit formula" sense: the nonconstructive D has no computable form.

### Semantic risks

| Risk | Assessment |
|---|---|
| Vacuity | No. `Function.invFun_apply` is a real theorem; `DomainPoint k` is nonempty (domainPoint_nonempty). |
| Proxy property | No. The statement IS D ∘ U = id. |
| Weakened claim | No. The conclusion is the full left-inverse condition. |
| Left-only claim misrepresented as full invertibility | No. The theorem is named `...left_inverse...`; it does not claim `U ∘ D = id`. |
| hScaleInj creating vacuity | No. hScaleInj is satisfiable (e.g., k = 0 makes R = 1 and r ↦ r² is injective on [0,∞)). |

### Verdict: PASS — statement matches intent; no semantic risk detected.

---

## Module Topology

Both NCL-00 and NCL-01 will be added to `openlensio_semantics/InjectivityModel.lean`.
Rationale:
- `InjectivityModel.lean` already contains `radialDescale`, `radialScale`, and all
  five UI-series injectivity theorems. The NCL theorems are a natural continuation
  of the same injectivity story.
- The file is 320 lines and will grow by ~80 lines — remains a normal-sized file.
- No new Lean file is needed; no imports change (InjectivityModel already imports
  DistortionModel, which imports RadialPolynomial, which imports LensSemantics,
  which imports Mathlib.Tactic).

### MODULE TOPOLOGY GATE:
- Is this task likely to create or reorganize Lean files: no
- Does the first slice have a file policy: yes — append to InjectivityModel.lean
- Stop before implementation unless this gate passes: gate passes.
