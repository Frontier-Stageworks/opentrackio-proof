# Proof Review — Local Existence and Uniqueness

## Review target

- Theorem / task slug: inverse-existence
- File: `inverse_approximation/InverseApproximation.lean` (append-only continuation)
- Theorem name: `D_exists_unique_preimage`
- Reviewed command: `/laps-start`

## Review evidence

- Repo commit: `852e7defe42f019737d594d21aacc8b5647d3a4d` (HEAD; this
  task's change uncommitted)
- Review date: 2026-08-16
- Review scope: one new theorem appended to an existing file
- Acceptance claim level: module (`InverseApproximation`), incremental
- Review type: exhaustive audit of the 1 new declaration (the 21
  pre-existing declarations are read-only, re-confirmed compiling, not
  re-audited)
- Strongest required Lean command run: yes — `lake build InverseApproximation`
  and `lake build` (whole repo), both pass
- Final Lean result: pass
- Warnings: one, pre-existing (`hR` unused in `radial_bounded`, unrelated to this task)
- Placeholder grep: clean (no `sorry`/`admit`/`axiom`/`unsafe`/`partial`)
- Axiom check: `#print axioms D_exists_unique_preimage` →
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`
- Scope evidence: `git status --short` shows only
  `inverse_approximation/InverseApproximation.lean` modified (append);
  `lakefile.toml` untouched, no new directory created — matches the user's
  explicit "same file, same module" constraint
- Artifact freshness: current — all Lean commands re-run after the final edit

## Time-box compliance (specific to this task's explicit constraint)

The user set a hard rule: stop after ~2-3 iterations on a single Mathlib
API/subtype friction point, document, and report a stopping point rather
than push through. This was **not triggered**. Evidence:

| Friction point | Iterations to resolve | Under budget? |
|---|---:|---|
| Scratch: `∃!` direction mismatch (`w=z` vs `z=w`) | 1 | yes |
| Real file: `hiff`'s `linear_combination` sign | 1 | yes |
| Real file: `MapsTo` namespace | 1 | yes |

No single point required more than 1 correction. The risk was actively
managed, not avoided by luck: the full architecture was validated in an
isolated scratch file *before* touching the real file (proof-plan.md),
which is why real-file integration only surfaced two small, real-file-
specific issues (a sign convention and a missing namespace qualifier) —
exactly the kind of low-severity friction the pre-validation was meant to
push earlier in the process, not eliminate entirely.

## Theorem statement (final, as compiled)

```lean
theorem D_exists_unique_preimage
    (θ : Coeffs) (R t : ℝ) (hR : 0 ≤ R)
    (hcontract : |t| * L θ R < 1)
    (y : ℂ) (hy : ‖y‖ + |t| * M θ R ≤ R) :
    ∃! z : ℂ, ‖z‖ ≤ R ∧ D θ t z = y
```

Matches the user's specification exactly, character for character.

## Kernel status

- Compiles: yes. No forbidden constructs.
- No existing declaration touched: confirmed by `git diff` — pure append.
- No `lakefile.toml`/new-directory change: confirmed.

## Statement audit (summary — full detail in statement-audit.md)

Matches user intent exactly. Correctly identified as the theorem
`docs/laps/inverse-injectivity/` explicitly deferred. Correctly scoped as
a standalone mathematical fact, with SQ-CV-07 relevance treated as a
separate, undetermined question (not conflated with the theorem's content)
— this distinction is checked explicitly below, not just asserted.

## Mathlib API integration review (the actual point of this task)

| Step | API used | Subtype friction? |
|---|---|---|
| Disk is closed | `Metric.isClosed_closedBall` (via set-equality to `closedBall`) | none |
| Closed ⟹ complete | `IsClosed.isComplete` | none — operates on the raw `Set`, no subtype |
| Self-mapping | `Set.MapsTo`, built directly from `inverse_step_maps_disk` | none |
| Contraction constant | `Real.coe_toNNReal` (real → `ℝ≥0`) | none, straightforward coercion |
| Lipschitz on restriction | `LipschitzWith.of_dist_le_mul` + `Subtype.dist_eq` | minimal — one `rintro ⟨a,ha⟩ ⟨b,hb⟩` destructuring, immediately closed |
| Existence | `ContractingWith.exists_fixedPoint'` (set-based, not bundled-subtype) | none — this is precisely why this entry point was chosen (AMB-IE-001) |
| Uniqueness | `ContractingWith.fixedPoint_unique'` on the two subtype-packaged fixed points, then `Subtype.ext`/`congrArg Subtype.val` | minimal — two `show`/`Subtype.ext` lines, mechanical |
| D ↔ inverseStep translation | local `hiff`, `linear_combination` | none (pure algebra, not API) |

The task's own premise — "the Brown-Conrady-specific mathematics is already
done, everything from here is Mathlib API integration" — held up: zero
uses of `Φ`, `M`, `L`'s explicit polynomial forms in this proof; every step
either quotes `inverse_step_maps_disk`/`inverse_step_lipschitz` as black
boxes or is generic completeness/fixed-point plumbing.

## Anti-pattern scan

Same clean result as prior sessions in this module — no statement
laundering, no vacuous theorem, no weakened conclusion (this is if
anything the *strongest* theorem in the file — existence AND uniqueness,
where priors only had injectivity or an error bound), no unused hypotheses
(`hR`, `hcontract`, `hy` all load-bearing), no tactic soup, no automation
hiding a hard step (the fixed-point existence itself is delegated to
`exists_fixedPoint'` by name, not hidden inside a broad `simp`/`aesop`
call), no scope violation (checked explicitly above).

## Required action

- Semantic proof action: none
- Verification/build action: none
- Process evidence action: none

## Final verdict

**accepted**

## Final notes

- This closes the loop opened by `docs/laps/inverse-injectivity/`'s own
  deferred-work note. `inverse_approximation/InverseApproximation.lean`
  now contains a complete local inversion theorem for the polynomial
  Brown-Conrady model, from first-principles boundedness/Lipschitz
  estimates through to existence and uniqueness — with every deferral
  along the way honored explicitly (no premature existence claims in
  earlier sessions) and then explicitly picked back up when attempted.
- Per the user's instruction, `D_exists_unique_preimage`'s relevance to
  SQ-CV-07 is recorded as a *separate, open* question in the doc updates
  that follow this review — this theorem proves a fact about the abstract
  model, not about what OpenTrackIO producers/consumers should do.
