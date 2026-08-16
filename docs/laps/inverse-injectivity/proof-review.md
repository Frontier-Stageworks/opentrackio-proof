# Proof Review — Inverse Injectivity

## Review target

- Theorem / task slug: inverse-injectivity
- File: `inverse_approximation/InverseApproximation.lean` (append-only
  continuation of the module from `docs/laps/bounded-inverse-approximation/`)
- Theorem name: 5 new/promoted theorems + 1 new definition (full inventory below)
- Reviewed command: `/laps-start`

## Review evidence

- Repo commit: `c54da5dcb70a76759a8a3c0c2919d05edb814f12` (HEAD; this task's
  change — the modified `InverseApproximation.lean` — is uncommitted)
- Review date: 2026-08-16
- Review scope: append-only addition to one existing file (module-level)
- Acceptance claim level: module (`InverseApproximation`), incremental
- Review type: exhaustive theorem audit of the 5 new/promoted declarations
  (the 8 pre-existing theorems from the prior session are out of scope —
  read-only, re-confirmed compiling, not re-audited)
- Strongest required Lean command run: yes — `lake build InverseApproximation`
  and `lake build` (whole repo), both pass
- Final Lean result: pass
- Warnings: one, pre-existing (`hR` unused in `radial_bounded`, not part of
  this task's changes)
- Search / grep command: `grep -REn --include="*.lean" "sorry|admit|set_option warn\.sorry|^unsafe|^partial|^axiom" inverse_approximation/InverseApproximation.lean`
- Search result: no matches (exit 1)
- Theorem declarations reviewed: 5 (+ 1 definition) — exact inventory via
  `grep -n "^theorem\|^noncomputable def"`:
  1. `smul_norm` (line 456)
  2. `D_eq_implies_eq` (line 476)
  3. `D_injective_on_disk` (line 501)
  4. `inverseStep` — definition (line 529)
  5. `inverse_step_maps_disk` (line 531)
  6. `inverse_step_lipschitz` (line 542)
- Inventory count type: exact
- Placeholder hygiene evidence: grep above, clean; `#print axioms` on all 5
  theorems returns exactly `[propext, Classical.choice, Quot.sound]`
- Scope evidence: `git status --short` shows only
  `inverse_approximation/InverseApproximation.lean` modified;
  `lakefile.toml`, `Pipeline/`, `DistortionConversion*.lean` untouched —
  matches the user's explicit scope requirement
- Artifact freshness status: current — all Lean commands re-run after the
  final code edit
- metrics.md required: yes (medium task); finalized: yes

## Theorem statements (final, as compiled)

```lean
theorem smul_norm (t : ℝ) (w : ℂ) : ‖t • w‖ = |t| * ‖w‖

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

All match the user's requested signatures exactly, with the one
pre-authorized deviation (`inverseStep` naming, AMB-II-001) applied
consistently to theorems 2–3 as offered.

## Kernel status

- Compiles: yes. No `sorry`/`admit`/unauthorized `axiom`/`unsafe`/`partial`: yes.
- No existing declaration touched: confirmed by `git diff` — the edit is a
  pure append (all changes are new lines at the end of the file; the
  8 pre-existing theorems and 8 pre-existing definitions are byte-identical).
- No `lakefile.toml`/`Pipeline/`/`DistortionConversion*.lean` change: confirmed.

## Statement audit (summary — full detail in statement-audit.md)

`D_eq_implies_eq` matches user intent exactly (standard contraction-implies-
injective argument). `D_injective_on_disk` is a genuinely thin corollary,
confirmed by zero API friction. `inverse_step_maps_disk`/
`inverse_step_lipschitz` are correctly scoped as Banach *prerequisites*,
not an existence claim — every doc-comment says so explicitly, matching
the user's requirement (a). Requirement (b) (q = |t|·L θ R as the shared
invertibility threshold) and (c) (polynomial-only scope, no unit
conversion, SQ-CV-07 not resolved) are both stated in the module-level
doc-comment added above `D_eq_implies_eq` and repeated for `inverseStep`.

## Scope-violation check (specific to this task's explicit constraints)

| Constraint | Checked how | Result |
|---|---|---|
| No Banach/fixed-point machinery | grep for `ContractingWith`, `CompleteSpace`, `Metric.complete`, `Function.invFun` in the file | none found |
| No new file/directory | `git status --short` | only the existing file modified |
| No `lakefile.toml` change | `git diff lakefile.toml` | empty |
| No existing theorem/def edited | `git diff` line-level review | pure append, confirmed |
| Doc-comments state (a)/(b)/(c) | manual read of both new doc-comment blocks | present in both |

## Hypothesis / conclusion audit

No vacuous or over-strong hypotheses found (statement-audit.md). `hcontract`
is the one genuinely load-bearing non-obvious hypothesis in this batch;
its necessity and non-vacuity are argued there.

## Automation review

`linear_combination` (one algebraic identity, verified against hand-checked
Mathlib-name testing before writing), bare `nlinarith` (the
contraction-forces-zero step, verified to need zero hints), `gcongr`,
`ring`, `simp only [Complex.real_smul]`. All goal-shaped; the one failure
this session (proof-run-log.md) was a `rw`-scope mistake, not an
automation-hides-the-hard-step issue — the fix made the proof MORE direct
(single calc from the target's LHS), not more automated.

## Anti-pattern scan

Same clean result as the prior session's review — no statement laundering,
no vacuous theorem, no weakened conclusion, no unused hypotheses (all 5
theorems' hypotheses are used), no tactic soup, no automation hiding a hard
step, no scope violation (checked explicitly above, unlike a generic scan).

## Required action

- Semantic proof action: none
- Verification/build action: none
- Process evidence action: none

## Final verdict

**accepted**

## Final notes

- This task's stated goal — prerequisites for a future Banach argument,
  not the argument itself — was verifiably respected, not just claimed:
  the scope-violation check above is a direct grep/diff audit, not an
  assertion.
- `D_eq_implies_eq` and `inverse_step_lipschitz` share the exact same
  contraction quantity `|t| * L θ R`, syntactically (not just
  conceptually) — confirmed by reading both statements side by side above.
  This is the concrete form of the user's requirement (b).
