# Proof Run Log — Bounded Inverse Approximation

## Parent theorem

- Theorem / task slug: bounded-inverse-approximation
- File: `inverse_approximation/InverseApproximation.lean`
- Command: `/laps-start` (medium task, implementation authorized by user's
  initial prompt, which specified exact theorem shapes)

## Project context

- Lean toolchain: `leanprover/lean4:v4.29.0`
- Package config: `lakefile.toml` (`InverseApproximation` lib added)
- Mathlib available: yes
- Target imports: TBD, resolved incrementally against actual `exact?` output
- Relevant local modules: none (self-contained, no repo imports beyond Mathlib)

## Lean command

```sh
lake env lean inverse_approximation/InverseApproximation.lean
lake build InverseApproximation
```

## Verification status

| Check | Command | Result | Notes |
|---|---|---|---|
| Narrow file check | `lake env lean inverse_approximation/InverseApproximation.lean` | pass | 1 warning: unused `hR` in `radial_bounded` (kept for signature parity with the other `radial_*`/`phi_*` theorems that DO use it; same style already established elsewhere in this repo) |
| Module build | `lake build InverseApproximation` | pass | `Build completed successfully (3286 jobs)` |
| Full repo build | `lake build` | pass | `Build completed successfully (3316 jobs)` — confirms the new independent module didn't affect anything else |
| Axiom check | `#print axioms` on all 8 theorems | pass | all depend on exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no custom axioms |
| Placeholder grep | `grep -REn "sorry\|admit\|set_option warn\.sorry\|^unsafe\|^partial\|^axiom"` | clean | exit 1, no matches |

## Pre-implementation lemma-name verification (done during Stop 1/2 planning)

Scratch-tested (files deleted after use, not committed) against this exact
Mathlib version:

| Fact needed | Lemma found |
|---|---|
| `‖a+b‖ ≤ ‖a‖+‖b‖` | `norm_add_le a b` |
| `‖a-b‖ ≤ ‖a‖+‖b‖` | `norm_sub_le a b` |
| `‖a‖-‖b‖ ≤ ‖a-b‖` | `norm_sub_norm_le a b` |
| `t • z = (t:ℂ) * z` | `Complex.real_smul` |
| `‖(t:ℂ)‖ = \|t\|` | `simp` closes it |
| `‖t•z‖ = \|t\|*‖z‖` | `rw [Complex.real_smul, norm_mul]; simp` |
| `\|z.re\| ≤ ‖z‖` | `Complex.abs_re_le_norm z` |
| `‖z‖^2 = Complex.normSq z` | `Complex.sq_norm z` |
| `Complex.normSq z = z.re*z.re+z.im*z.im` | `Complex.normSq_apply z` |
| `a^n ≤ b^n` from `0≤a≤b` | `pow_le_pow_left₀ ha h n` |

Not yet verified (needed during Stop 3): `‖z‖ ≤ \|z.re\|+\|z.im\|`-shaped
lemma or inline proof; `module`/`ring` closing the composition identity;
`positivity` on `M θ R`, `L θ R`.

## Attempts / Failures / Successful hard steps

Implementation proceeded in the exact order planned (definitions →
`radial_bounded` → `normSq_lipschitz` → `normSq_sq_lipschitz` →
`normSq_cube_lipschitz` → `radial_lipschitz` → `phi_bounded` →
`phi_lipschitz` → `inverse_approx_error`), each checked with `lake env lean`
before moving to the next.

### Failures (all resolved within one correction, no repeated tactic paths)

1. **`radial_bounded`, first draft**: used `apply le_trans (abs_add _ _)` +
   nested `gcongr`/`exact abs_add _ _` for the 3-term triangle inequality.
   Errors: `Unknown identifier abs_add` (this Mathlib version's 2-term
   triangle inequality for `abs` is not named `abs_add`), plus "No goals to
   be solved"/"too many tactics" from the resulting malformed tactic
   sequence. Root cause: guessed a lemma name instead of checking. Fix:
   `exact?`-verified `abs_add_three` for the 3-term case, closes in one
   line. Fixed once, not repeated elsewhere in the file for the 3-term
   pattern (used consistently thereafter).

2. **`phi_bounded`, `hre_sq_le`**: first draft used a malformed
   `abs_le_abs`/`neg_le_of_neg_le` chain (type mismatch: `-R ≤ -|z.re|` fed
   where `-|z.re|^2 ≤ z.re^2` was expected). Root cause: over-engineered a
   one-line fact. Fix: `nlinarith [sq_abs z.re, hre, abs_nonneg z.re]`
   directly — closes immediately given the right fact list.

3. **`phi_bounded`, `gcongr` calls**: two `gcongr` goals left an unsolved
   side condition `0 ≤ Mrad θ R` (gcongr can't see through the `Mrad`
   definition automatically). Fix: added `have hMrad_nonneg : 0 ≤ Mrad θ R
   := by unfold Mrad; positivity` before the calc block; `gcongr` then
   found it in context automatically.

4. **`phi_bounded`, trailing `ring` after an `abs_of_nonneg`-terminated
   `rw` chain**: "No goals to be solved" twice (the `rw` chain's last
   rewrite already closed the goal, matching the calc step's RHS exactly;
   the extra `ring` had nothing left to do). Fix: deleted the two redundant
   `ring` calls.

5. **`phi_lipschitz`**: same `abs_add`→`abs_add_le` naming issue as failure
   1, but for the 2-term case this time (7 occurrences across `hterm1`,
   `hterm1'`, `hterm2`, `hterm3a`, `hterm3b`, and two inline calc steps
   inside `hΦx`/`hΦy`). Fixed with one `sed` substitution across the file
   after `exact?`-confirming `abs_add_le` is the correct name, not repeated
   individually.

6. **`inverse_approx_error`, `hid`**: first draft used `rw [smul_sub]; abel`
   to prove the composition identity. Error: `rewrite` did not find the
   `?r • (?x - ?y)` pattern (the goal's `t • (Φ θ x - Φ θ (D θ t x))` on the
   RHS didn't syntactically match after `unfold`, likely due to how `D`
   unfolds inline). Fix: `simp only [Complex.real_smul]; ring` — converts
   all `t • w` to `(t:ℂ) * w` first, then it's pure ring arithmetic over
   `ℂ`, which `ring` closes directly. This is the CORRECTED-sign identity
   from `statement-audit.md` Correction 1 — confirmed by Lean, not just by
   hand.

7. **`inverse_approx_error`, final `calc` step**: `rw [sq_abs t] ▸ (by
   ring)` was malformed term-mode syntax. Fix: `rw [← sq_abs t]; ring` as a
   tactic block.

No `ALGEBRA STOP` was triggered — every failure was resolved within the
two-attempt tripwire budget, and each was a naming/syntax issue caught
immediately by the narrow Lean check, not a genuine algebraic dead end. The
hand-derived closed forms for `M`, `L` (algebra-plan.md) matched what Lean
actually needed with zero adjustment — the algebra-first-then-Lean-second
discipline paid off here.

### Successful hard step: `phi_lipschitz`

The theorem the whole task's difficulty was expected to concentrate in
(per `proof-plan.md`'s risk assessment) compiled with only the one naming
fix (failure 5) — no algebraic dead ends. The product-difference identity
(`u₁u₂-v₁v₂ = u₁(u₂-v₂)+(u₁-v₁)v₂`, proved by `ring` at each of 2 use
sites) plus the pre-derived `radial_lipschitz`/`normSq_lipschitz` building
blocks reduced the whole proof to mechanical `calc` chains with `gcongr`
closing each monotonicity step — exactly the outcome the algebra-plan.md
telescoping strategy was designed to produce.

## Metrics counters

- Lean runs: 9 narrow checks (one per declaration added) + 1 module build +
  1 full repo build + 1 axiom-check run = 12
- Failed tactic attempts: 7 (listed above), all resolved on the next attempt
- Repeated tactic paths: 0
- Algebra stops: 0
- Proof stops: 0
- Conceptual stops: 0
- Human interventions: 0
- Helper lemmas added: 4 top-level (`normSq_lipschitz`, `normSq_sq_lipschitz`,
  `normSq_cube_lipschitz`, `radial_lipschitz`) + 2 local defs (`Mrad`,
  `Lrad`) — more than the 2 anticipated in proof-plan.md, because the
  `normSq_*` telescoping steps were promoted to named top-level lemmas
  rather than kept as inline `have`s, since `radial_lipschitz` needed all
  three and readability favored naming them (still within "medium task,
  one theorem plus helper lemmas" scope, not scope creep)
- Theorem statement changes requested: 0 (2 proof-step corrections made
  during planning, recorded in ambiguity-register.md — not statement
  changes, see statement-audit.md; both confirmed correct by the Lean
  proof itself, see failure 6 above)
- Definition changes requested: 0

---

(Log entries appended chronologically below.)
