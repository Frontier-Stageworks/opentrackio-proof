# Proof Review — Bounded Inverse Approximation

## Review target

- Theorem / task slug: bounded-inverse-approximation
- File: `inverse_approximation/InverseApproximation.lean`
- Theorem name: 8 theorems (full inventory below)
- Reviewed command: `/laps-start` (implementation authorized by the user's
  initial prompt, which specified exact theorem shapes for a medium task)

## Review evidence

- Repo path / identifier: `opentrackio-proof` (local working tree)
- Repo commit: `ae87ec2bf782bf37e4ddbc69cdbded30218e28b8` (HEAD at review
  time; this task's files are new/uncommitted — `lakefile.toml` modified,
  `inverse_approximation/` and `docs/laps/bounded-inverse-approximation/`
  untracked)
- LAPS version: skill bundle as installed at `~/.claude/commands/laps/laps`
- Review date: 2026-08-16
- Review scope: one new file (module-level)
- Acceptance claim level: module (`InverseApproximation`)
- Review type: exhaustive theorem audit (of this one new file — no other
  file's theorems are re-audited here)
- Strongest required Lean command: `lake build InverseApproximation`
  (module-level claim) — also ran `lake build` (whole repo) to confirm no
  side effects, though whole-repo acceptance is not being claimed here
- Strongest required Lean command run: yes
- Final Lean command: `lake env lean inverse_approximation/InverseApproximation.lean`
  (exit 0, 1 warning); `lake build InverseApproximation` (`Build completed
  successfully (3286 jobs)`); `lake build` (`Build completed successfully
  (3316 jobs)`)
- Final Lean result: pass (all three)
- Warnings: one, `unused variable hR` in `radial_bounded` — kept for
  signature parity with the other 7 theorems in this file, all of which
  genuinely use their `hR : 0 ≤ R` hypothesis; `radial_bounded`'s proof
  happens not to need it directly (nonnegativity of `R` isn't separately
  invoked — the bound follows from `‖z‖≤R` and `‖z‖≥0` alone). Not a defect;
  a consistent-signature choice, matching the pattern already established
  in `Pipeline/PixelSufficiency.lean`/`Pipeline/PixelIffCorrected.lean`
  elsewhere in this repo (unused `hF_pos` kept for parity).
- Search / grep command(s): `grep -REn --include="*.lean" "sorry|admit|set_option warn\.sorry|^unsafe|^partial|^axiom" inverse_approximation/InverseApproximation.lean`
- Search / grep result(s): no matches (exit 1)
- Search command executability: all executable
- Lean files reviewed: 1 (new)
- Theorem declarations reviewed: 8 — exact inventory via `grep -n "^theorem "`:
  1. `radial_bounded` (line 88)
  2. `normSq_lipschitz` (line 118)
  3. `normSq_sq_lipschitz` (line 133)
  4. `normSq_cube_lipschitz` (line 155)
  5. `radial_lipschitz` (line 183)
  6. `phi_bounded` (line 214)
  7. `phi_lipschitz` (line 261)
  8. `inverse_approx_error` (line 417)
- Inventory count type: exact
- Inventory command or method: `grep -n "^theorem " inverse_approximation/InverseApproximation.lean`
- Theorem inventory attached: yes (above)
- Exhaustive claim allowed: yes
- Placeholder hygiene evidence: grep above, clean; `#print axioms` on all 8
  theorems returns exactly `[propext, Classical.choice, Quot.sound]` for
  each — no `sorryAx`, no custom axioms
- Diagnostics evidence: see proof-run-log.md verification-status table
- Artifact freshness status: current — all Lean commands re-run after the
  final code edit, before this review
- metrics.md required: yes (medium task, algebra-heavy)
- metrics.md finalized: yes
- Evidence gaps: none for the module-level claim made here

## Classification consistency check

- Final Lean result known: yes
- Warnings known: yes
- Strongest required Lean command run for claimed scope: yes
- `lake build` run (whole repo, informational): yes, pass
- Search commands executable: yes
- Theorem inventory exact: yes
- Metrics status recorded: yes
- Verdict/evidence consistent: yes
- Required Action split present: yes (below)

## Theorem statements (final, as compiled)

```lean
theorem radial_bounded (θ : Coeffs) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    |radial θ z| ≤ Mrad θ R

theorem normSq_lipschitz (R : ℝ) (a b : ℂ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    |Complex.normSq a - Complex.normSq b| ≤ 2 * R * ‖a - b‖

theorem normSq_sq_lipschitz (R : ℝ) (hR : 0 ≤ R) (a b : ℂ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    |(Complex.normSq a) ^ 2 - (Complex.normSq b) ^ 2| ≤ 4 * R ^ 3 * ‖a - b‖

theorem normSq_cube_lipschitz (R : ℝ) (hR : 0 ≤ R) (a b : ℂ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    |(Complex.normSq a) ^ 3 - (Complex.normSq b) ^ 3| ≤ 6 * R ^ 5 * ‖a - b‖

theorem radial_lipschitz (θ : Coeffs) (R : ℝ) (hR : 0 ≤ R) (a b : ℂ)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    |radial θ a - radial θ b| ≤ Lrad θ R * ‖a - b‖

theorem phi_bounded (θ : Coeffs) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖Φ θ z‖ ≤ M θ R

theorem phi_lipschitz (θ : Coeffs) (R : ℝ) (hR : 0 ≤ R) (a b : ℂ)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖Φ θ a - Φ θ b‖ ≤ L θ R * ‖a - b‖

theorem inverse_approx_error (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R) (x : ℂ)
    (hx : ‖x‖ + |t| * M θ R ≤ R) :
    ‖U θ t (D θ t x) - x‖ ≤ L θ R * M θ R * t ^ 2
```

All match `proof-capsule.md`'s specification-level texts exactly (the
`Mrad`/`Lrad`/`normSq_*` helper theorems were anticipated in the algebra
plan even though not all were pre-named in the capsule's theorem-text list —
see proof-run-log.md "Helper lemmas added" for the count reconciliation).

## Kernel status

- File compiles: yes
- Full build passes: yes
- No `sorry`/`admit`/unauthorized `axiom`/`constant`/`unsafe`/`partial`: yes (all)
- No forbidden theorem-statement changes: n/a — all 8 theorems are new,
  nothing existing was touched. `git status` confirms this task's changes
  are exactly `lakefile.toml` (one new `[[lean_lib]]` block, verified via
  `git diff lakefile.toml`) plus the two new directories.
- No unauthorized definition changes: n/a (all new)
- No unauthorized import changes: yes — one new `[[lean_lib]]` entry,
  pre-authorized in the capsule; the file itself imports only
  `Mathlib.Tactic`
- No unauthorized global `[simp]`/`[grind]`/`grind_pattern`: yes (none used)

## Statement audit (summary — full detail in statement-audit.md)

Plain-English `inverse_approx_error` (the theorem the task exists to
produce):

> On a disk of radius R (with a buffer margin accounting for the
> worst-case displacement), the naive first-order approximate inverse of
> the scaled polynomial Brown-Conrady distortion map has composition error
> bounded by L·M·t², where L and M are explicit closed-form Lipschitz/
> boundedness constants.

Matches user intent: yes, with two recorded proof-engineering corrections
(composition-identity sign; buffer hypothesis design) that do not change
theorem intent — see `statement-audit.md`. Both corrections were
independently *confirmed correct* by the compiled Lean proof, not just
argued by hand (see proof-run-log.md failure 6 for the sign correction
specifically).

## Hypothesis audit

| Name | Role | Used? | Necessary? | Suspicious? |
|---|---|---:|---:|---:|
| `hR : 0 ≤ R` (7 of 8 theorems) | domain | yes (7/8; unused in `radial_bounded`, kept for parity) | yes | no |
| `hz`/`ha`/`hb : ‖·‖ ≤ R` | disk membership | yes | yes | no |
| `hx : ‖x‖ + \|t\|·M θ R ≤ R` (`inverse_approx_error` only) | buffer margin | yes (derives both `‖x‖≤R` and `‖D θ t x‖≤R`) | yes | no — this is the one non-obvious hypothesis in the file; its necessity and non-vacuity are explicitly argued in statement-audit.md and ambiguity-register.md AMB-BIA-002, not silently introduced |

No vacuous or self-implying hypothesis found.

## Conclusion audit

- Conclusion strong enough / not weakened / not a proxy property: yes to
  all — `inverse_approx_error`'s conclusion is exactly the `L·M·t²` bound
  requested, with `L`, `M` the same closed-form functions used in the two
  standalone estimate theorems (not different, weaker constants)
- Expresses a semantic property, not an implementation artifact: yes

## Proof strategy / hard-step identification

Direct algebraic estimate throughout — no fixed-point/contraction
machinery used anywhere in the file (confirmed by inspection: no
`ContractingWith`, no `Metric.complete`, no `Function.invFun`, no import
beyond `Mathlib.Tactic`), matching the user's explicit instruction. The
hard step, as anticipated in proof-plan.md, was `phi_lipschitz`'s
multi-term difference bound — resolved via the product-difference identity
(`u₁u₂-v₁v₂ = u₁(u₂-v₂)+(u₁-v₁)v₂`) applied uniformly across both
components, built on the pre-derived `radial_lipschitz`/`normSq_*` chain.
Each `calc` step is individually auditable; no step relies on opaque
automation closing more than a single, locally-obvious monotonicity or
ring-identity fact (`gcongr` and `ring` are used only after the hard
algebraic content has already been isolated into an explicit equality or
factored form via a preceding `have`/`rw`).

## Automation review

Automation used: `ring`, `gcongr`, `positivity`, `nlinarith`, `linarith`,
`simp` (narrowly, e.g. `simp only [Complex.real_smul]`), `abel`. All
goal-shaped, none opaque — see proof-run-log.md for the one place
(`inverse_approx_error`'s `hid`) where an initial automation choice
(`abel` after `smul_sub`) failed and was replaced with a more direct
`simp only [Complex.real_smul]; ring`, itself then confirmed by the kernel.

## Anti-pattern scan

| Anti-pattern | Found? | Notes |
|---|---:|---|
| Statement laundering | no | |
| Vacuous theorem | no | see hypothesis audit |
| Weakened conclusion | no | |
| Over-strong hypotheses | no | buffer hypothesis is the minimal addition needed, justified in ambiguity-register.md |
| Unused hypotheses | yes (1) | `hR` in `radial_bounded`, parity choice, documented |
| Tactic soup | no | structured `calc` chains throughout |
| Automation hiding hard step | no | |
| Fixed-point/contraction machinery used (would be scope violation) | no | confirmed by import/lemma-name inspection |
| Layer 5 (unit conversion) folded in | no | file is self-contained, no `F`/mm/pixel anywhere |
| `Pipeline/`/`DistortionConversion*` touched | no | zero imports, zero edits confirmed via `git status`/`git diff` |

## Required action

- Semantic proof action: none
- Verification/build action: none (fresh checks already run)
- Process evidence action: none

## Rejection criteria check

None triggered (statement matches intent, non-vacuous, no forbidden
constructs, compiles, hard step not hidden).

## Artifact freshness check

| Artifact | Status |
|---|---|
| `proof-capsule.md` | current |
| `statement-audit.md` | current — both corrections confirmed by the compiled proof |
| `ambiguity-register.md` | current |
| `proof-plan.md` | current |
| `algebra-plan.md` | current — every hand-derived bound matched what Lean needed with zero numeric adjustment |
| `proof-run-log.md` | current, updated after final Lean check |
| `metrics.md` | updated (see below) |

Lean check timing: run after the last code edit — yes. Theorem count in
file (8) matches theorem count in this review (8) — yes.

## Metrics finalization

- metrics.md required: yes
- metrics.md updated after final Lean command: yes
- final score recorded: yes (see metrics.md)

## Final verdict

**accepted**

## Final notes

- Layers 4 (existence/uniqueness via fixed-point) and 5 (unit conversion)
  are explicitly and verifiably out of scope — confirmed by inspection,
  not just by intent.
- This task does not resolve SQ-CV-07 (D-U/U-D question) — it produces the
  bounded-error estimate that SQ-CV-07 itself said would be needed for any
  future progress on that question, nothing more. `docs/limitations.md`
  and `docs/specification-questions.md` are updated to say exactly this,
  additively, without softening existing language.
