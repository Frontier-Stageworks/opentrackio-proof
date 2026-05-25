---
name: undistort-invertibility-ambiguity-register
description: Ambiguity register for the undistort invertibility campaign — tracks unresolved questions about invertibility scope, D definition, and coefficient conditions
metadata:
  type: reference
---

# Ambiguity Register — Undistort Invertibility Campaign

**Task slug:** `undistort-invertibility`
**Date:** 2026-05-24

Inherits all unresolved entries from `openlensio-semantics/ambiguity-register.md`.
This register adds new ambiguities specific to the invertibility campaign.

---

## AMB-UI-001 — No closed-form forward distortion D for general Brown-Conrady (INHERITED, CRITICAL)

**Source:** AMB-OL-010 (openlensio-semantics ambiguity register)
**Status:** Partially resolved — framing corrected after re-reading spec (2026-05-24)

**Framing correction (post-campaign):** The original framing said "the spec does not
provide D." This is imprecise. Reading the spec directly:

- Eq (5): `ε_d = U⁻¹(ε_u − ΔC − ΔP) + ΔC + ΔP`
- Eq (11): `ε'_d = U⁻¹(ε'_u − ΔC) + ΔC`, "which can be solved using numerical iterative methods depending on the application."

The spec DOES define D = U⁻¹ as a mathematical object in both equations. It asserts D
exists. The numerical iteration note is about *computing* D at a specific input — not
about whether D is defined. The spec treats U as invertible without proving it.

**What is actually open:** The Lean formalization challenge is that there is no
closed-form formula for D for the full Brown-Conrady model. In Lean, to use D you must
either: (a) construct D nonconstructively via `Function.invFun` given injectivity (which
we have proved in several regimes), yielding `D ∘ U = id` by injectivity alone; (b) find
a closed-form D for a restricted subclass and prove it (which UI-04 did for p=0 with
`radialDescale`); or (c) use IFT to prove a local inverse exists without constructing it.

**Proof impact:** REVISED. A theorem of the form `D ∘ U = id` CAN be stated using
`Function.invFun` once U is proved injective on a domain — no concrete closed-form D is
required. The campaign's injectivity results (UI-00 through UI-03) are sufficient inputs
for a nonconstructive left-inverse theorem. The more informative concrete result
(UI-04/`radialDescale`) is also proved for p=0.

**Remaining open:** Proving U is surjective onto its intended range (needed for U ∘ D = id
in the `Function.invFun` sense). Global injectivity without the `hScaleInj` hypothesis
(item 5 in the next-steps file). These are the actual open gates, not D's definition.

---

## AMB-UI-002 — Scope of injectivity: global vs local vs on-circle

**Status:** Partially resolved — UI-00 on-circle p=0, UI-01 global p=0, UI-03 on-circle full p

**What is the issue:** "Injectivity of U" can mean:
1. U is injective on each circle of fixed radius (proof: U reduces to pure scaling when p=0)
2. U is injective on all of ℝ² (requires monotonicity of R(r)*r and a tangential argument)
3. U is locally injective near each point (requires Jacobian nonzero)

The campaign proceeds from 1 → 2 → 3 in stages. Only stage 1 is in the first slice.

**Proof impact:** Medium. The theorem statement changes significantly between these cases.
Do not overstate: UI-00 proves on-circle injectivity, not global injectivity.

**Resolution for UI-00:** On-circle injectivity only. Hypothesis `hSameR` enforces this.

---

## AMB-UI-003 — Coefficient conditions for R(r) ≠ 0

**Status:** Resolved (SLICE-UI-02)

**Resolution:** Per-point polynomial positivity of numerator and denominator:
- `hNum : 0 < 1 + k.k1 * r^2 + k.k3 * r^4 + k.k5 * r^6`
- `hDen : 0 < 1 + k.k2 * r^2 + k.k4 * r^4 + k.k6 * r^6`

These are minimal sufficient conditions for `R(r) > 0`. No global coefficient constraints
are imposed. Proved in `radialTerm_pos`; corollary `radialTerm_ne_zero` discharges `hR₁`
in `undistortPoint_injective_pure_radial`.

---

## AMB-UI-004 — Monotonicity of f(r) = R(r) * r for pure-radial injectivity

**Status:** Unresolved

**What is the issue:** For SLICE-UI-01 (global pure-radial injectivity without `hSameR`),
the proof requires that f(r) = R(r)*r is strictly monotone on [0, ∞). This is a real-analysis
claim about a rational function. It requires:
1. f'(r) > 0 for all r in the domain, OR
2. f is injective by a direct argument (hard without derivatives)

Mathlib may have tools (e.g., `StrictMonoOn`, `deriv`, `HasDerivAt`) but the proof
would require computing the derivative of a rational function and showing it is positive
under coefficient conditions.

**Implementation risk:** High. This is the main bottleneck for SLICE-UI-01. Do not
attempt UI-01 until this approach is analyzed.

**Proposed resolution:** Defer to UI-01 planning. For UI-00, the `hSameR` hypothesis
avoids this entirely.

---

## AMB-UI-005 — Whether to define D as a new function or use existential

**Status:** Resolved (SLICE-UI-04)

**Resolution:** Concrete D for the p = 0 subclass: `radialDescale k r hr ε = ⟨ε.x / R(r), ε.y / R(r)⟩`.
The explicit radius parameter r reflects AMB-UI-001: no closed-form D from the output alone.
Theorem `radialDescale_left_inverse_zero_tangential` proves D(r, U(ε)) = ε when p = 0, R(r) ≠ 0.
An existential variant (using `Function.invFun`) is derivable from UI-00's injectivity but was
not needed — the concrete D for p = 0 is more informative.

**Important caveat (added post-campaign):** `radialDescale` is a *conditional* left inverse, not
a local inverse in the standard sense. A local inverse of U at ε₀ would be a function of the
output alone — g : SensorPoint → SensorPoint with g(U(ε)) = ε near ε₀ and no extra parameters.
`radialDescale` requires r = sensorRadius(ε) as an explicit input, meaning the caller already
knows the input radius. Recovering r from U(ε) alone requires inverting r ↦ R(r)·r, which is
precisely what AMB-UI-001 says requires numerical iteration. The campaign does not prove existence
of a local inverse; it proves a conditional left inverse whose conditionality is the formal record
of the open gap.
