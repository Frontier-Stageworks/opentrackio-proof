---
name: inverse-injectivity-proof-plan
description: Proof plan for smul_norm, D_eq_implies_eq, D_injective_on_disk, inverseStep, inverse_step_maps_disk, inverse_step_lipschitz
metadata:
  type: project
---

# Proof Plan — Inverse Injectivity

All Mathlib facts below were scratch-verified against this exact Mathlib
version before writing this plan (proof-capsule.md). No algebra-plan.md is
needed for this task — every proof is a short, direct application of
already-proved `phi_bounded`/`phi_lipschitz` plus one elementary
contraction argument; there is no new multi-term polynomial estimate to
derive (unlike the previous task).

## `smul_norm`

- Goal shape: equality. Opening move: `rw [Complex.real_smul, norm_mul];
  simp` — identical to the existing local `hsmul_norm` inside
  `inverse_approx_error`, promoted to top-level (AMB-II-002).

## `D_eq_implies_eq`

- Goal shape: equality `a = b` from an equational hypothesis `hD` plus a
  numeric contraction hypothesis.
- Opening move: derive `heq : a - b = -(t • (Φ θ a - Φ θ b))` from `hD` via
  `unfold D at hD; simp only [Complex.real_smul] at hD ⊢; linear_combination hD`
  (verified in proof-capsule.md).
- Then: `‖a-b‖ = |t| * ‖Φ θ a - Φ θ b‖` (via `heq`, `norm_neg`, `smul_norm`),
  bound `‖Φ θ a - Φ θ b‖ ≤ L θ R * ‖a-b‖` via `phi_lipschitz θ R hR a b ha
  hb`, combine to `‖a-b‖ ≤ |t|*L θ R*‖a-b‖`.
- Hard step (the only genuinely new *idea* in this task, though a short
  one): "contraction forces zero" — `nlinarith` closes `n = 0` directly
  from `0 ≤ n`, `q < 1`, `n ≤ q*n` with **no hints needed** (verified).
  Then `norm_eq_zero.mp` + `sub_eq_zero.mp` to conclude `a = b`.
- Automation budget: one bare `nlinarith` for the contraction step (already
  confirmed to work); `linear_combination` for the algebraic identity;
  no `field_simp` needed anywhere (no division in this theorem).

## `D_injective_on_disk`

- Goal shape: `Set.InjOn`. Opening move: `intro a ha b hb hDab; exact
  D_eq_implies_eq θ R t hR hcontract a b ha hb hDab` — direct application,
  confirmed to compose with zero membership-unfolding friction.

## `inverseStep`, `inverse_step_maps_disk`

- Definition: `y - t • Φ θ z` (AMB-II-001).
- Goal shape: inequality. Opening move: `unfold inverseStep`, then
  `calc ‖y - t•Φθz‖ ≤ ‖y‖+‖t•Φθz‖ := norm_sub_le _ _` `_ = ‖y‖+|t|*‖Φθz‖ :=
  by rw [smul_norm]` `_ ≤ ‖y‖+|t|*M θ R := by gcongr [phi_bounded θ R hR z hz]`
  `_ ≤ R := hy`. Direct, no hard step — this is literally
  `inverse_approx_error`'s own `hDxR` derivation, restated as a standalone
  theorem about `T_y` (statement-audit.md).

## `inverse_step_lipschitz`

- Goal shape: inequality. Opening move: `unfold inverseStep`, derive
  `heq : (y - t•Φθa) - (y - t•Φθb) = -(t•(Φθa-Φθb))` via `simp only
  [Complex.real_smul]; ring`, then `rw [heq, norm_neg, smul_norm]`, then
  bound via `phi_lipschitz θ R hR a b ha hb` and `gcongr`/`ring`. Direct, no
  hard step.

## Slice plan

Single slice. Implementation order: `smul_norm` → `D_eq_implies_eq` →
`D_injective_on_disk` → `inverseStep` def → `inverse_step_maps_disk` →
`inverse_step_lipschitz`, narrow `lake env lean` check after each.
