---
name: nonconstructive-left-inverse-ambiguity-register
description: Ambiguity register for the nonconstructive left-inverse campaign (NCL-00, NCL-01)
metadata:
  type: reference
---

# Ambiguity Register — Nonconstructive Left Inverse

**Task slug:** `nonconstructive-left-inverse`

---

## Summary Table

| ID | Title | Affects | Status |
|---|---|---|---|
| AMB-NCL-001 | `hR_all` — global vs. per-point R ≠ 0 | theorem shape, hypothesis design | Resolved by design |
| AMB-NCL-002 | `Nonempty (DomainPoint k)` required by `Function.invFun_apply` | instance design | Resolved — r=0 witness |
| AMB-NCL-003 | `hScaleInj` open hypothesis inherited from UI-01 | proof completeness | Carried forward (open item 5) |
| AMB-NCL-004 | Left inverse only — right inverse (surjectivity) is not addressed | scope | Design choice, documented |

---

## AMB-NCL-001: `hR_all` — global vs. per-point R ≠ 0

**Severity:** low

**Description:**

`undistortPoint_injective_pure_radial` (UI-01) takes `hR₁ : radialTerm k (sensorRadius ε₁) h₁ ≠ 0`
as a per-point hypothesis about the *first* argument `ε₁`. For
`Function.Injective (undistortSub k p)`, which quantifies over *all* domain point pairs,
we need R ≠ 0 for every domain point, not just a specific one.

**Resolution (by design):**

The injectivity wrapper takes:
```lean
hR_all : ∀ (ε : SensorPoint) (h : denominatorNonzero k (sensorRadius ε)),
    radialTerm k (sensorRadius ε) h ≠ 0
```
This is the minimal global condition. Callers can discharge it using `radialTerm_ne_zero`
(UI-02) per-point, or by providing per-point hNum/hDen conditions. The hypothesis is
honest — it is necessary for injectivity (R=0 at some point would break it) and sufficient
(proof applies `hR_all ε₁ h₁` to get `hR₁`).

**Status:** Resolved by design (2026-05-25).

---

## AMB-NCL-002: `Nonempty (DomainPoint k)` required by `Function.invFun_apply`

**Severity:** low — mechanical resolution

**Description:**

`Function.Injective.invFun_apply` in Mathlib requires `[Nonempty α]` where α is the domain
type. In our case α = `DomainPoint k`. If this instance is missing, Lean will fail to
elaborate the one-liner proof in NCL-01.

**Resolution:**

`DomainPoint k = {ε : SensorPoint // denominatorNonzero k (sensorRadius ε)}`.
At ε = ⟨0, 0⟩:
- `sensorRadius ⟨0, 0⟩ = Real.sqrt (0² + 0²) = Real.sqrt 0 = 0`
- `denominatorNonzero k 0 = (1 + k.k2·0² + k.k4·0⁴ + k.k6·0⁶ ≠ 0) = (1 ≠ 0)` ✓

So `⟨0, 0⟩ : SensorPoint` is always a domain point for any `k`. Define:
```lean
instance domainPoint_nonempty (k : RadialCoefficients) : Nonempty (DomainPoint k) :=
  ⟨⟨⟨0, 0⟩, by simp [denominatorNonzero, sensorRadius]; norm_num⟩⟩
```

The exact tactic may need adjustment (e.g., `Real.sqrt_zero` may need to be unfolded
manually), but the mathematical content is unambiguous.

**Status:** Resolved by design (2026-05-25). Instance to be proved in NCL-00.

---

## AMB-NCL-003: `hScaleInj` open hypothesis inherited from UI-01

**Severity:** medium (mathematical open item, not a proof defect)

**Description:**

`undistortSub_injective_pure_radial` and `undistortSub_nonconstructive_left_inverse_pure_radial`
both carry:
```lean
hScaleInj : ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
    (radialScale k r₁) ^ 2 * r₁ ^ 2 = (radialScale k r₂) ^ 2 * r₂ ^ 2 → r₁ = r₂
```

This hypothesis asserts that the function r ↦ (R(r)·r)² is injective on [0,∞). It was
inherited from UI-01 (`undistortPoint_injective_pure_radial`) and is the open item from
next-steps.md item 5 ("Radial Term Monotonicity / Injectivity").

**Why not discharged here:**

Proving hScaleInj requires resolving a coefficient-constraint design question
(restrict to a bounded interval, or identify a coefficient constraint guaranteeing global
positivity of the derivative numerator). This is a separate campaign with its own
proof-plan design. See next-steps.md item 5 for details.

The hypothesis is satisfiable: for k = {0,0,0,0,0,0} (all-zero), R(r) = 1 and
r ↦ r² is injective on [0,∞). Non-vacuous.

**Status:** Open. Carried forward from AMB-UI-004. Blocking full unconditional injectivity.

---

## AMB-NCL-004: Left inverse only — right inverse not addressed

**Severity:** informational — scope boundary

**Description:**

`undistortSub_nonconstructive_left_inverse_pure_radial` proves D ∘ U = id (left inverse).
It does NOT prove U ∘ D = id (right inverse), which would require showing U is surjective
onto some target range.

Surjectivity of U for general p is not addressed in this project and is blocked by:
- No characterization of the image of U for general p.
- Surjectivity for the pure-radial case would require showing every w ∈ ℝ² can be
  written as R(|ε|)·ε for some ε; this is closely related to surjectivity of r ↦ R(r)·r
  on [0,∞), which is also open (next-steps item 5).

**Status:** Design boundary (2026-05-25). No action required for this campaign.
The theorem is named `...left_inverse...` to make the one-directional nature explicit.
