---
name: undistort-invertibility-proof-capsule
description: Proof capsule for the undistort invertibility campaign — injectivity and invertibility properties of undistortPoint; staged from same-radius restriction to full model
metadata:
  type: reference
---

# Proof Capsule — Undistort Invertibility Campaign

**Task slug:** `undistort-invertibility`
**Command:** `laps-start`
**Date:** 2026-05-24
**Phase:** Stop 1
**Task size:** large

---

## 1. User Intent

Prove that the Brown-Conrady undistortion map U (defined as `undistortPoint` in
`DistortionModel.lean`) is an isomorphism — that a forward distortion function D exists
and that D ∘ U = id and U ∘ D = id. The original description: "the current work proves
one arrow of an isomorphism but not that it's actually an isomorphism."

---

## 2. Fundamental Constraint (Must Appear in Every Slice Review)

The OpenLensIO v1.0.1 spec explicitly states, following Eq (11), that U⁻¹ "can be solved
using numerical iterative methods depending on the application." This characterises the
inverse as a numerical approximation, not a closed-form function.

**Consequence:** No closed-form forward distortion function D exists for the general
Brown-Conrady model. The campaign cannot prove D ∘ U = id for a general closed-form D.

**What can be proved instead:**
- Injectivity of U under restricted conditions (necessary condition for invertibility)
- Injectivity in the pure radial case (p = 0) via function-of-radius analysis
- Existence of a local inverse via the Implicit Function Theorem (Mathlib machinery)
- Explicit forward distortion for the degenerate constant-R case

The campaign proceeds in stages; each stage must be authorized before the next begins.
`AMB-OL-010` remains unresolved and gates the full invertibility claim.

---

## 3. Load-Bearing Definitions (Forbidden to Change Without Authorization)

| Definition | File | Role |
|---|---|---|
| `denominatorNonzero k r` | `RadialPolynomial.lean` | Per-point domain predicate: `1 + k.k2*r² + k.k4*r⁴ + k.k6*r⁶ ≠ 0` |
| `radialTerm k r h` | `RadialPolynomial.lean` | Rational radial factor R = numerator/denominator; ignores `h` in body |
| `undistortX k p ε h` | `DistortionModel.lean` | x-component: `R*ε.x + 2*p1*ε.x*ε.y + p2*(r² + 2*ε.x²)` |
| `undistortY k p ε h` | `DistortionModel.lean` | y-component: `R*ε.y + p1*(r² + 2*ε.y²) + 2*p2*ε.x*ε.y` |
| `undistortPoint k p ε h` | `DistortionModel.lean` | Full U: `⟨undistortX k p ε h, undistortY k p ε h⟩` |
| `sensorRadius p` | `CoordinateTypes.lean` | `√(p.x² + p.y²)` |

**Critical property of `radialTerm`:** The `h : denominatorNonzero k r` argument is
bound as `_` in the body — it is not used in the computation. `radialTerm k r h₁ = radialTerm k r h₂`
for any two proofs of the same type. This enables clean reasoning about equal-radius
pairs without proof-term manipulation.

---

## 4. Existing Supporting Lemmas

| Lemma | File | Role |
|---|---|---|
| `tangential_zero_coefficients_identity` | `DistortionModel.lean` | p=0 → `undistortX = R * ε.x` |
| `brown_conrady_zero_identity` | `DistortionModel.lean` | all k,p=0 → U(ε) = ε |
| `radial_zero_coefficients_identity` | `RadialPolynomial.lean` | all k=0 → R = 1 |
| `SensorPoint.ext` | `CoordinateTypes.lean` | `.x` and `.y` equality → `SensorPoint` equality |

---

## 5. Selected First Slice Theorem (SLICE-UI-00)

**Informal statement:** If p₁ = p₂ = 0 (no tangential distortion), the two input points
have the same sensor radius (lie on the same circle centered at the distortion origin), the
radial term at that radius is nonzero, and the two undistorted outputs are equal, then the
two inputs are equal.

**Proposed Lean statement:**

```lean
theorem undistortPoint_injective_zero_tangential
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (hp1 : p.p1 = 0) (hp2 : p.p2 = 0)
    (ε₁ ε₂ : SensorPoint)
    (h₁ : denominatorNonzero k (sensorRadius ε₁))
    (h₂ : denominatorNonzero k (sensorRadius ε₂))
    (hR : radialTerm k (sensorRadius ε₁) h₁ ≠ 0)
    (hSameR : sensorRadius ε₁ = sensorRadius ε₂)
    (hU : undistortPoint k p ε₁ h₁ = undistortPoint k p ε₂ h₂) :
    ε₁ = ε₂
```

**Why this is the right shape:**
- The `hSameR` hypothesis is natural: both points lie on the same circle. U is a
  pure radial scaling R(r)*ε when p = 0; on a fixed circle, the scaling factor is
  the same for all points. If the outputs are equal under the same scaling, the inputs
  must be equal (when R ≠ 0).
- This avoids the hard step of proving R(r)*r is monotone (needed for general
  pure-radial injectivity without `hSameR`).
- The `hR ≠ 0` hypothesis is necessary: if R = 0 then U maps all points on the
  circle to the origin, destroying injectivity.

**Plain English:** On each circle centered at the distortion origin, the zero-tangential
Brown-Conrady map is injective when R ≠ 0.

---

## 6. Proof Engineering Level

Stop 1 (this capsule): conceptual modeling and theorem decomposition.
Selected first slice: proving a fixed theorem (SLICE-UI-00).

---

## 7. Allowed Changes for SLICE-UI-00

- Local `have` statements
- Unfolding `undistortPoint`, `undistortX`, `undistortY`, `radialTerm`, `denominatorNonzero`
- Use of `simp only [...]` with the above definitions
- Use of `tangential_zero_coefficients_identity` and `SensorPoint.ext`
- Use of `mul_left_cancel₀` (Mathlib, works over ℝ with `NoZeroDivisors`)
- Use of `congr_arg`, `congr`, `ext`
- One new Lean file: `openlensio_semantics/InjectivityModel.lean`
- Adding `InjectivityModel` target to `lakefile.toml`

## 8. Forbidden Changes for SLICE-UI-00

- Modifying any existing theorem statement in `DistortionModel.lean` or `RadialPolynomial.lean`
- Modifying any load-bearing definition listed in Section 3
- `sorry`, `admit`, unauthorized `axiom`, `unsafe`, `partial`
- Global `[simp]` annotations added to satisfy a local goal
- Implementing SLICE-UI-01 through UI-04 (deferred slices)
- Defining a forward distortion function D (deferred to UI-03 or UI-04)
- Claiming full invertibility from the injectivity result
