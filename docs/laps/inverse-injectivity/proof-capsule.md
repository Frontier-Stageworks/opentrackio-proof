---
name: inverse-injectivity-capsule
description: Proof capsule for D-injectivity under a contraction condition and the two Banach-prerequisite estimates (self-mapping, contraction) for the fixed-point iteration step, continuing inverse_approximation/InverseApproximation.lean
metadata:
  type: project
---

# Proof Capsule — Inverse Injectivity (Layers 1–3 continuation)

## Intent (plain English)

Direct continuation of `docs/laps/bounded-inverse-approximation/` (layers
1–3: `Φ`, `D`, `U`, `M`, `L`, `phi_bounded`, `phi_lipschitz`,
`inverse_approx_error`), same file, same module. Three new results:

1. **`D_eq_implies_eq`** — the forward map `D θ t` is injective on the disk
   `‖·‖ ≤ R` whenever `|t| * L θ R < 1` (a contraction condition on the
   displacement field's Lipschitz constant). Proof: if `D θ t a = D θ t b`,
   then `a - b = -t•(Φ θ a - Φ θ b)`, so `‖a-b‖ ≤ |t|·L θ R·‖a-b‖`; since
   `|t|·L θ R < 1`, this forces `‖a-b‖ = 0`.
2. **`inverse_step_maps_disk`** — the fixed-point iteration map
   `T_y(z) = y - t•Φ θ z` (used by a Picard-iteration-style construction of
   the true inverse, NOT attempted here) maps the disk into itself when `y`
   satisfies the same buffer condition `‖y‖ + |t|·M θ R ≤ R` used by
   `inverse_approx_error`.
3. **`inverse_step_lipschitz`** — `T_y` is itself a contraction (Lipschitz
   constant `|t|·L θ R`) on the disk.

Together, (2) and (3) are exactly the two hypotheses a Banach fixed-point
argument would need to conclude `T_y` has a unique fixed point (the true
inverse `D θ t⁻¹(y)`) — but that argument itself (existence, via
`CompleteSpace`/`ContractingWith`/subtype API) is **explicitly out of
scope** for this task, per the user's instruction. This task produces the
*prerequisites*, not the existence proof.

`q := |t| * L θ R` is the natural invertibility threshold throughout: it is
literally the same quantity in `D_eq_implies_eq`'s contraction hypothesis
and `inverse_step_lipschitz`'s conclusion — the same number will govern any
future existence proof.

## Explicitly out of scope (separate, later task — do not start here)

- Existence of the true inverse of `D θ t` via Banach fixed-point
  (`ContractingWith`, `CompleteSpace`, subtype/closed-ball API integration).
- Any change to `M`, `L`, `Φ`, `D`, `U`, or the four existing theorems
  (`radial_bounded`, `radial_lipschitz`, `phi_bounded`, `phi_lipschitz`,
  `inverse_approx_error`, plus the three `normSq_*` helpers) — all read-only
  in this task.
- `F`/mm/pixel unit conversion (layer 5).
- Resolving `docs/specification-questions.md` SQ-CV-07.
- New directory or `lean_lib` entry — this is the *same* file, *same*
  module (`InverseApproximation`), no `lakefile.toml` change.

## Lean grounding

- Same file: `inverse_approximation/InverseApproximation.lean` (appended to,
  nothing existing edited)
- Same imports: `Mathlib.Tactic` only (no new import needed — confirmed via
  scratch-testing every lemma used below against this exact Mathlib
  version before writing this capsule)
- Reuses (read-only): `Φ`, `D`, `M`, `L`, `phi_bounded`, `phi_lipschitz`

## Pre-verified Mathlib facts (scratch-tested before any Lean code)

```lean
example (t : ℝ) (a b p q : ℂ) (hD : a + t • p = b + t • q) :
    a - b = -(t • (p - q)) := by
  simp only [Complex.real_smul] at hD ⊢; linear_combination hD

example (z : ℂ) (h : ‖z‖ = 0) : z = 0 := norm_eq_zero.mp h

example (t Lval n : ℝ) (hn : 0 ≤ n) (hc : |t| * Lval < 1) (hle : n ≤ |t| * Lval * n) :
    n = 0 := by nlinarith

example (P : ℂ → Prop) (f : ℂ → ℂ)
    (h : ∀ a, P a → ∀ b, P b → f a = f b → a = b) :
    Set.InjOn f {z : ℂ | P z} := fun a ha b hb hfab => h a ha b hb hfab
```

All four resolve cleanly — including the bare `nlinarith` closing the
contraction-forces-zero step with no hints, and `Set.InjOn` composing
directly with the raw injectivity implication (no membership-unfolding
friction). This means the optional `D_injective_on_disk` corollary the user
asked for ("if it composes cleanly ... skip if API friction") **does**
compose cleanly and will be included.

## Theorem texts (exact, as specified by the user; one modeling choice noted below)

```lean
theorem D_eq_implies_eq
    (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R)
    (hcontract : |t| * L θ R < 1)
    (a b : ℂ)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R)
    (hD : D θ t a = D θ t b) :
    a = b

theorem D_injective_on_disk (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R)
    (hcontract : |t| * L θ R < 1) :
    Set.InjOn (D θ t) {z : ℂ | ‖z‖ ≤ R}
```

```lean
noncomputable def inverseStep (θ : Coeffs) (t : ℝ) (y z : ℂ) : ℂ := y - t • Φ θ z

theorem inverse_step_maps_disk
    (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R) (y z : ℂ)
    (hy : ‖y‖ + |t| * M θ R ≤ R) (hz : ‖z‖ ≤ R) :
    ‖inverseStep θ t y z‖ ≤ R

theorem inverse_step_lipschitz
    (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R) (y a b : ℂ)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖inverseStep θ t y a - inverseStep θ t y b‖ ≤ |t| * L θ R * ‖a - b‖
```

**Modeling choice**: introducing `inverseStep θ t y z := y - t • Φ θ z` and
stating theorems 2–3 in terms of it, per the user's explicit "use your
judgment" permission — reasoning in `ambiguity-register.md` AMB-II-001.

## New reusable helper (additive, does not touch any existing theorem)

```lean
theorem smul_norm (t : ℝ) (w : ℂ) : ‖t • w‖ = |t| * ‖w‖
```

Promoted to a top-level lemma because it is now needed by 4 proofs total
(the pre-existing `inverse_approx_error`, which keeps its own local
`have hsmul_norm` unchanged — not touched — plus the 3 new theorems here).
See `ambiguity-register.md` AMB-II-002.

## Allowed changes

- Append the definitions/theorems above to
  `inverse_approximation/InverseApproximation.lean`.
- Small local `have`s inside the new proofs.
- Short additive notes in `docs/limitations.md` and
  `docs/specification-questions.md` SQ-CV-07 (per user instruction).

## Forbidden changes

- No edit to any existing declaration in `InverseApproximation.lean`.
- No edit to `Pipeline/`, `DistortionConversion*.lean`, `lakefile.toml`.
- No Banach/`ContractingWith`/`CompleteSpace` existence machinery.
- `sorry`, `admit`, unauthorized `axiom`, `unsafe`, `partial` forbidden.
