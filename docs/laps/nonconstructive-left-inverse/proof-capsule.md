---
name: nonconstructive-left-inverse-proof-capsule
description: Proof capsule for the nonconstructive left-inverse theorem (D ∘ U = id via Function.invFun)
metadata:
  type: reference
---

# Proof Capsule — Nonconstructive Left Inverse

**Task slug:** `nonconstructive-left-inverse`
**Date started:** 2026-05-25
**Repo commit at start:** `494947f8f84032390c560148d87fe8ce2c115a87`
**Model:** claude-sonnet-4-6
**Command:** `laps-start`
**Parent campaigns:** undistort-invertibility (UI-00 through UI-04)

---

## Goal

Prove a nonconstructive left-inverse theorem for the Brown-Conrady undistortion map U
restricted to the pure-radial subcase (p₁ = p₂ = 0).

In plain English: for every sensor point ε in the domain (where the radial denominator
is nonzero), the Mathlib-defined nonconstructive inverse `Function.invFun (undistortSub k p)`
satisfies `D(U(ε)) = ε`. This formally instantiates the spec's claim that D = U⁻¹
(OpenLensIO Eqs 5 and 11) for the pure-radial subcase.

---

## Motivation

The undistort-invertibility campaign (UI-00 through UI-04) proved several injectivity
results for undistortPoint. However, the actual left-inverse conclusion — that a D exists
satisfying D ∘ U = id — was not stated formally. The present campaign closes that gap
for the pure-radial case using Mathlib's nonconstructive left-inverse machinery.

This is item 1 from next-steps.md (the highest-priority next step after UI-04).

---

## Domain Typing Problem and Solution

`undistortPoint k p ε h` carries a proof argument `h : denominatorNonzero k (sensorRadius ε)`,
making its type `(ε : SensorPoint) → denominatorNonzero k (sensorRadius ε) → SensorPoint`.
This is not a plain function `SensorPoint → SensorPoint`, so `Function.Injective` cannot
be applied directly.

**Solution — subtype approach:**

Define `DomainPoint k := {ε : SensorPoint // denominatorNonzero k (sensorRadius ε)}`.
Define `undistortSub k p : DomainPoint k → SensorPoint` as the plain wrapper.
The injectivity result from UI-01 lifts to `Function.Injective (undistortSub k p)`,
which is exactly what `Function.Injective.invFun_apply` needs.

---

## Theorem Statements (Proposed)

### Slice NCL-00: Definitions and injectivity wrapper

```lean
-- Domain subtype: sensor points where the radial denominator is nonzero
def DomainPoint (k : RadialCoefficients) : Type :=
  {ε : SensorPoint // denominatorNonzero k (sensorRadius ε)}

-- Wrapper: undistortPoint as a plain function on DomainPoint k
noncomputable def undistortSub (k : RadialCoefficients) (p : TangentialCoefficients) :
    DomainPoint k → SensorPoint :=
  fun ⟨ε, h⟩ => undistortPoint k p ε h

-- Nonempty instance (needed by Function.invFun_apply):
-- (0,0) is always a domain point because denominator = 1 ≠ 0 at r = 0
instance domainPoint_nonempty (k : RadialCoefficients) : Nonempty (DomainPoint k) :=
  ⟨⟨⟨0, 0⟩, by simp [denominatorNonzero, sensorRadius]; norm_num⟩⟩

-- Injectivity of undistortSub for pure-radial case
theorem undistortSub_injective_pure_radial
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (hp1 : p.p1 = 0) (hp2 : p.p2 = 0)
    (hR_all : ∀ (ε : SensorPoint) (h : denominatorNonzero k (sensorRadius ε)),
        radialTerm k (sensorRadius ε) h ≠ 0)
    (hScaleInj : ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
        (radialScale k r₁) ^ 2 * r₁ ^ 2 = (radialScale k r₂) ^ 2 * r₂ ^ 2 → r₁ = r₂) :
    Function.Injective (undistortSub k p)
```

### Slice NCL-01: Main theorem

```lean
-- Nonconstructive left inverse: for every domain point εd,
--   (Function.invFun (undistortSub k p)) (undistortSub k p εd) = εd
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

---

## Objects and Parameters

| Name | Type | Role |
|---|---|---|
| `k` | `RadialCoefficients` | Six radial coefficients k1–k6 |
| `p` | `TangentialCoefficients` | Tangential coefficients p1, p2 |
| `hp1`, `hp2` | props | Pure-radial restriction |
| `hR_all` | hypothesis | R ≠ 0 for all domain points (global lift of UI-01's hR₁) |
| `hScaleInj` | hypothesis | Radial scaling r ↦ (R·r)² is injective on [0,∞) (from UI-01) |
| `DomainPoint k` | subtype | {ε : SensorPoint // denominatorNonzero k (sensorRadius ε)} |
| `undistortSub k p` | function | `DomainPoint k → SensorPoint`, plain wrapper around undistortPoint |
| `εd` | `DomainPoint k` | Arbitrary domain point |

---

## Load-Bearing Definitions

| Definition | Intended meaning | Status |
|---|---|---|
| `DomainPoint k` | sensor points where the radial denominator is nonzero | new — NCL-00 |
| `undistortSub k p` | undistortPoint wrapped as a plain function on DomainPoint | new — NCL-00 |
| `undistortPoint` | Brown-Conrady undistortion map U (DistortionModel.lean) | existing, not modified |
| `denominatorNonzero` | radial denominator ≠ 0 predicate (RadialPolynomial.lean) | existing, not modified |
| `radialScale` | radial factor R(r) without proof argument (InjectivityModel.lean) | existing, not modified |

---

## Relation to Prior Work

| Prior result | Role in this campaign |
|---|---|
| `undistortPoint_injective_pure_radial` (UI-01) | Lifted to function-level injectivity via subtype wrapper |
| `radialTerm_ne_zero` (UI-02) | Can discharge `hR_all` per-point; not used directly in proofs |
| `radialDescale_left_inverse_zero_tangential` (UI-04) | Concrete left inverse (requires explicit r); this campaign proves existential left inverse using only the output |

---

## What This Proves vs. What It Does Not

**Proves:** `D(U(ε)) = ε` for all `ε : DomainPoint k` when p=0 and hScaleInj holds.
This is D ∘ U = id on DomainPoint k restricted to the pure-radial case.

**Does not prove:**
- `U(D(u)) = u` for all u (right inverse / surjectivity — requires a separate argument).
- Global left inverse for general p (tangential case blocked by on-circle restriction of UI-03).
- The injectivity of hScaleInj itself (open item, next-steps item 5).
- A closed-form formula for D (remains blocked by AMB-UI-001).

---

## Allowed Changes (NCL-00)

- New definition `DomainPoint k`
- New definition `undistortSub k p`
- New instance `domainPoint_nonempty`
- New theorem `undistortSub_injective_pure_radial`
- Local `have`s and `intro` destruction in proofs
- Use of `Subtype.ext`, `Function.Injective`, existing project lemmas

## Allowed Changes (NCL-01)

- New theorem `undistortSub_nonconstructive_left_inverse_pure_radial`
- Use of `Function.Injective.invFun_apply` (key Mathlib lemma)

## Forbidden Changes (Both Slices)

- No modification of `undistortPoint`, `undistortX`, `undistortY`, `denominatorNonzero`, `radialTerm`, `radialScale`, or any prior theorem
- No `sorry`, `admit`, unauthorized `axiom`, `unsafe`, `partial`
- No weakening of hypothesis set (in particular: `hScaleInj` must be carried, not silently discharged by a restrictive coefficient assumption)
- No global `@[simp]` annotations for local goals
- No implementation of right-inverse or surjectivity (deferred)
