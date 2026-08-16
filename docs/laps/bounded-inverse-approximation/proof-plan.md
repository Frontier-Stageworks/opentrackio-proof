---
name: bounded-inverse-approximation-proof-plan
description: Proof plan for phi_bounded, phi_lipschitz, and inverse_approx_error in inverse_approximation/InverseApproximation.lean
metadata:
  type: project
---

# Proof Plan — Bounded Inverse Approximation

## Definitions to write first (no theorems yet)

```lean
structure Coeffs where
  k1 : ℝ
  k2 : ℝ
  k3 : ℝ
  p1 : ℝ
  p2 : ℝ

noncomputable def radial (θ : Coeffs) (z : ℂ) : ℝ :=
  θ.k1 * Complex.normSq z + θ.k2 * (Complex.normSq z)^2 + θ.k3 * (Complex.normSq z)^3

noncomputable def Φ (θ : Coeffs) (z : ℂ) : ℂ :=
  ⟨radial θ z * z.re + 2*θ.p1*z.re*z.im + θ.p2*(Complex.normSq z + 2*z.re^2),
   radial θ z * z.im + θ.p1*(Complex.normSq z + 2*z.im^2) + 2*θ.p2*z.re*z.im⟩

noncomputable def D (θ : Coeffs) (t : ℝ) (x : ℂ) : ℂ := x + t • Φ θ x
noncomputable def U (θ : Coeffs) (t : ℝ) (y : ℂ) : ℂ := y - t • Φ θ y

noncomputable def M (θ : Coeffs) (R : ℝ) : ℝ :=
  2*|θ.k1|*R^3 + 2*|θ.k2|*R^5 + 2*|θ.k3|*R^7 + 5*|θ.p1|*R^2 + 5*|θ.p2|*R^2

noncomputable def L (θ : Coeffs) (R : ℝ) : ℝ :=
  6*|θ.k1|*R^2 + 10*|θ.k2|*R^4 + 14*|θ.k3|*R^6 + 10*|θ.p1|*R + 10*|θ.p2|*R
```

`radial` is defined via `Complex.normSq` directly (not a separately-named
`r2`/`r4`/`r6`) so that the boundedness/Lipschitz behavior of `radial` can
reuse Mathlib's `Complex.normSq`/`Complex.sq_norm` lemmas without a manual
`r² = ‖z‖²` bridging step at every use site.

## Theorem 1: `phi_bounded`

- Goal shape: inequality, `‖Φ θ z‖ ≤ M θ R` from `0 ≤ R`, `‖z‖ ≤ R`.
- Opening move: unfold `Φ` to expose `Φx := (Φ θ z).re`, `Φy := (Φ θ z).im`;
  bound `‖Φ θ z‖ ≤ |Φx| + |Φy|` (needs a `Complex.abs_le_abs_re_add_abs_im`-
  shaped lemma — confirm exact name at Stop 3 via `exact?`; if absent, prove
  inline via `Real.sqrt_le_sqrt` monotonicity + `nlinarith [abs_nonneg Φx,
  abs_nonneg Φy]` on the squared inequality `Φx²+Φy² ≤ (|Φx|+|Φy|)²`).
- Expected hard step: bounding `|Φx|`, `|Φy|` individually. Plan: a `have
  hradial : |radial θ z| ≤ Mrad θ R` first (`Mrad θ R := |k1|R²+|k2|R⁴+|k3|R⁶`,
  a genuine local helper, see `algebra-plan.md`), then bound `|Φx|` via
  triangle inequality (`abs_add`, `abs_add three-way`) + `abs_mul` +
  monotonicity (`mul_le_mul` chains) using `|z.re| ≤ R`, `|z.im| ≤ R`
  (from `Complex.abs_re_le_norm`/`Complex.abs_im_le_norm` + `hz`),
  `Complex.normSq z ≤ R^2` (from `Complex.sq_norm` + `hz` + monotonicity of
  squaring), and `hradial`. Close numeric combination with `nlinarith`
  supplied the abs-value nonnegativity facts and the coefficient/`R` bounds
  explicitly (not bare `nlinarith` — see algebra-plan.md's tripwire budget).
- Automation budget: one `nlinarith` per component bound (`|Φx|`, `|Φy|`),
  each supplied an explicit fact list; if either fails twice, emit
  `ALGEBRA STOP` and fall back to a fully `have`-chained derivation (see
  algebra-plan.md's per-monomial breakdown as the fallback).

## Theorem 2: `phi_lipschitz`

- Goal shape: inequality, `‖Φ θ a - Φ θ b‖ ≤ L θ R * ‖a - b‖`.
- Opening move: same `|Φx(a)-Φx(b)| + |Φy(a)-Φy(b)|` decomposition as
  Theorem 1, then decompose each into named pieces via the **product-
  difference identity** `u₁u₂ - v₁v₂ = u₁(u₂-v₂) + (u₁-v₁)v₂`, NOT via
  coordinate-by-coordinate polynomial expansion (rejected during planning as
  needlessly complex — see `algebra-plan.md` for why the `‖a‖²-‖b‖²`-style
  approach via `Complex.normSq`/`radial` as a single real-valued function of
  `a`, `b` is far simpler than expanding `Φx` as a degree-7 single-variable
  polynomial by fixing one coordinate).
- Expected hard step: a chain of "radial is itself bounded and Lipschitz"
  helper facts (`radial_bounded`, `radial_lipschitz` — promoted to named
  local lemmas, not just `have`s, since both `phi_bounded` and
  `phi_lipschitz` need `radial_bounded`), built from `Complex.normSq`
  difference-of-squares/cubes identities. Full derivation in
  `algebra-plan.md`.
- Helper lemmas (all local `private`/plain `theorem`/`lemma` in the same
  file, justified: reused across `phi_bounded` and `phi_lipschitz`, and
  each is a self-contained, nameable fact — not a `have` because they're
  used from two different top-level proofs):
  - `radial_bounded : ‖z‖ ≤ R → |radial θ z| ≤ |θ.k1|*R^2+|θ.k2|*R^4+|θ.k3|*R^6`
  - `radial_lipschitz : ‖a‖ ≤ R → ‖b‖ ≤ R → |radial θ a - radial θ b| ≤
    (2*|θ.k1|*R+4*|θ.k2|*R^3+6*|θ.k3|*R^5) * ‖a-b‖`
- Automation budget: same two-attempt-then-isolate rule as Theorem 1, per
  monomial/piece.

## Theorem 3: `inverse_approx_error`

- Goal shape: inequality from a universal-in-`x` context plus the buffer
  hypothesis.
- Opening move:
  1. `have hxR : ‖x‖ ≤ R` from the buffer hypothesis (`|t|*M θ R ≥ 0` since
     `M θ R ≥ 0` for `R ≥ 0`, itself from `M`'s definition being a sum of
     `|·| * R^odd`, all nonneg when `R ≥ 0` — a `positivity`-shaped fact,
     try `positivity` first).
  2. `have hDxR : ‖D θ t x‖ ≤ R` — unfold `D`, triangle inequality
     (`norm_add_le`), `‖t • Φ θ x‖ = |t| * ‖Φ θ x‖` (scalar-norm identity,
     confirmed available), `phi_bounded` at `x` (using `hxR`), then
     `linarith` with the buffer hypothesis.
  3. `have hid : U θ t (D θ t x) - x = t • (Φ θ x - Φ θ (D θ t x))` — unfold
     `U`, `D`; this should be a `module`/`ring`-normalizable vector identity
     over `ℂ` (smul distributes over `ℂ` as a module; likely closes via
     `simp [D, U, smul_sub]` + `ring`, or `module` tactic if available in
     this Mathlib version — confirm at Stop 3). Uses the CORRECTED sign
     from `statement-audit.md` Correction 1.
  4. `have hclose : ‖Φ θ x - Φ θ (D θ t x)‖ ≤ L θ R * ‖x - D θ t x‖` — direct
     `phi_lipschitz` application at `a := x`, `b := D θ t x`, using `hxR`,
     `hDxR`.
  5. `have hdiff : ‖x - D θ t x‖ = |t| * ‖Φ θ x‖` — unfold `D`,
     `sub_add_cancel'`-style simplification + scalar-norm identity.
  6. Combine: `‖U θ t (D θ t x) - x‖ = |t| * ‖Φ θ x - Φ θ (D θ t x)‖` (from
     `hid` + scalar-norm identity) `≤ |t| * (L θ R * ‖x - D θ t x‖)` (from
     `hclose`) `= |t| * (L θ R * (|t| * ‖Φ θ x‖))` (from `hdiff`) `≤ |t| *
     (L θ R * (|t| * M θ R))` (from `phi_bounded` at `x` via `hxR`) `= L θ R
     * M θ R * t^2` (algebra: `|t|*|t| = t^2` via `sq_abs` or `abs_mul_self`,
     then `ring`/`nlinarith`). This last combination step needs `L θ R ≥ 0`
     to preserve the inequality direction when multiplying by `L θ R` — a
     `positivity`-shaped side fact, prove alongside `M θ R ≥ 0`.
- Expected hard step: step 6's chain of inequality/equality combination —
  plan to do it as one `calc` block for auditability rather than a single
  opaque `nlinarith`/`gcongr` call, so each transition is visible and
  independently checkable (this is the composition-error theorem the whole
  task exists to produce — it must not be the one place automation hides
  what's happening).
- Automation budget: `positivity` for the two nonnegativity side facts;
  `linarith`/`nlinarith` for small numeric combinations within the `calc`
  chain; no bare `simp`/`aesop` on the main goal.

## Theorem-discovery approach

All Mathlib lemma names used above (`norm_add_le`, `norm_sub_le`,
`Complex.real_smul`, `norm_mul`, `Complex.abs_re_le_norm`, `Complex.sq_norm`,
`Complex.normSq_apply`, `pow_le_pow_left₀`) were confirmed to resolve against
this exact Mathlib version via scratch `exact?`/direct-term checks before
this plan was written (see `proof-capsule.md`). Remaining names needed
during Stop 3 (e.g. the `|Φx|+|Φy|` bound, `module`/`ring` closing the
composition identity, `positivity` on `M`/`L`) will be confirmed the same
way — via `exact?`/`apply?`, not guessed.

## Slice plan

Single continuous slice (medium task, one proof domain). Order of
implementation: definitions → `radial_bounded` → `radial_lipschitz` →
`phi_bounded` → `phi_lipschitz` → `inverse_approx_error`, each checked with
`lake env lean` before moving to the next (per the dependency order above —
`phi_bounded`/`phi_lipschitz` both need the two `radial_*` helpers first).
