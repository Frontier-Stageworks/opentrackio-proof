# Proof Review — Approximate-Inverse Error Relative to a True Preimage

## Review target

- Theorem / task slug: inverse-approx-error
- File: `inverse_approximation/InverseApproximation.lean` (append-only continuation)
- Theorem names: `inverse_approx_error_vs_preimage`, `inverse_approx_exists_unique_with_error`
- Reviewed command: `/laps-start`

## Review evidence

- Repo commit: `203967660076b992263fc20fcbffdbf6dfd767c7` (HEAD; this
  task's change uncommitted)
- Review date: 2026-08-16
- Review scope: 2 new theorems appended to an existing file
- Acceptance claim level: module (`InverseApproximation`), incremental
- Review type: exhaustive audit of the 2 new declarations (the 23
  pre-existing declarations are read-only, re-confirmed compiling, not re-audited)
- Strongest required Lean command run: yes — `lake build InverseApproximation`
  and `lake build` (whole repo), both pass
- Warnings: one, pre-existing (`hR` unused in `radial_bounded`, unrelated)
- Placeholder grep: clean
- Axiom check: both theorems → `[propext, Classical.choice, Quot.sound]`
- Scope evidence: `git status --short` shows only
  `inverse_approximation/InverseApproximation.lean` modified (append);
  `lakefile.toml`, `Pipeline/`, `DistortionConversion*.lean` untouched
- Artifact freshness: current — all Lean commands re-run after the final edit

## Theorem statements (final, as compiled)

```lean
theorem inverse_approx_error_vs_preimage
    (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R)
    (hcontract : |t| * L θ R < 1)
    (y z : ℂ) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) (hDz : D θ t z = y) :
    ‖U θ t y - z‖ ≤ (|t| ^ 2 * L θ R * M θ R) / (1 - |t| * L θ R)

theorem inverse_approx_exists_unique_with_error
    (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R)
    (hcontract : |t| * L θ R < 1)
    (y : ℂ) (hy : ‖y‖ + |t| * M θ R ≤ R) :
    ∃! z : ℂ, ‖z‖ ≤ R ∧ D θ t z = y ∧
      ‖U θ t y - z‖ ≤ (|t| ^ 2 * L θ R * M θ R) / (1 - |t| * L θ R)
```

Both match the user's specification exactly, character for character.

## Factoring-shape check (the actual point of this task)

| Requirement | Verified how | Result |
|---|---|---|
| Theorem 1 self-contained, no Banach machinery | grep for `ContractingWith`/`CompleteSpace`/`exists_fixedPoint` inside theorem 1's proof body (lines 669–712) | none found |
| Theorem 1 doesn't quietly depend on theorem 2 | theorem 1 compiles and was checked standalone, appended and verified *before* theorem 2 existed in the file | confirmed by build order in this session |
| Theorem 2 is a thin wrapper | line count: 6 lines of proof (`hM_nonneg`, `hyR`, `obtain`, `refine`, `rintro`, `exact`) | thin, as required — did not need to stop and report |
| Weakest hypothesis (`‖y‖≤R`, not buffer) at theorem 1 | hand-derived in statement-audit.md *before* writing Lean, confirming `phi_bounded` is only ever applied at `y` and `z` directly, never at a constructed image point | confirmed sufficient, no substitution made |
| Existence machinery used *only* in theorem 2 | `D_exists_unique_preimage` (the only existence-machinery-using theorem in the file) is invoked exactly once, inside theorem 2's proof, nowhere in theorem 1 | confirmed |

## Notable finding, disclosed not hidden

`AMB-IAE-001`: theorem 1's own hypotheses support a strictly tighter,
denominator-free bound directly from steps 1–3 (no triangle inequality, no
`hcontract`). The prescribed derivation (triangle inequality + division)
was implemented anyway, as the general-purpose Banach a priori pattern the
task's detailed outline clearly intended — not silently swapped for the
shortcut. See `ambiguity-register.md` for full reasoning.

## Kernel status

- Compiles: yes. No forbidden constructs.
- No existing declaration touched: confirmed by `git diff` — pure append.
- No `Pipeline/`/`DistortionConversion*.lean`/`lakefile.toml` change: confirmed.
- No reopening of `phi_bounded`/`phi_lipschitz`/`radial_bounded`/`radial_lipschitz`:
  confirmed — both proofs only ever *apply* these (and `inverse_step_lipschitz`,
  `smul_norm`, `D_exists_unique_preimage`) as black boxes.

## Hypothesis audit

| Hypothesis | Theorem | Used? |
|---|---|---:|
| `hR`, `hcontract`, `hy`, `hz`, `hDz` | `inverse_approx_error_vs_preimage` | all yes, in the prescribed (non-shortcut) proof — see statement-audit.md's table |
| `hR`, `hcontract`, `hy` | `inverse_approx_exists_unique_with_error` | all yes (`hR`/`hcontract` passed through to both sub-theorems; `hy` split into the buffer-derived `hyR` and the raw buffer fact itself) |

No vacuous or unused hypotheses in either theorem.

## Anti-pattern scan

No statement laundering, no vacuous theorem, no weakened conclusion, no
unused hypotheses, no tactic soup, no automation hiding a hard step (the
`nlinarith` calls are each preceded by explicit `have`s isolating exactly
the algebraic facts needed — `hDq`, `hkey` — not thrown at the raw goal),
no scope violation (checked explicitly above).

## Required action

- Semantic proof action: none
- Verification/build action: none
- Process evidence action: none

## Final verdict

**accepted**

## Final notes

- This is the fastest of the four sessions building out this module (2
  small, mechanical fixes total, both in theorem 1; theorem 2 compiled on
  the first attempt) — a direct result of doing the full hand-derivation
  and scratch-testing the flagged friction point (the division step)
  *before* writing anything in the real file. The division step, the one
  explicitly flagged as highest-risk, needed zero changes once integrated.
- The two fixes that did occur (`abel` not closing a shape it closed
  elsewhere in the file; `unfold` not auto-closing a reflexivity goal)
  were both in territory the scratch test didn't cover, because the
  scratch test used generic real-number stand-ins and never exercised the
  specific `U`/`inverseStep`/`Φ` unfolding shapes — consistent with the
  pattern observed in the `inverse-existence` session (generic-architecture
  scratch tests catch the hard/risky part; real-file integration still
  needs its own small, low-risk fixes for the specific definitions involved).
