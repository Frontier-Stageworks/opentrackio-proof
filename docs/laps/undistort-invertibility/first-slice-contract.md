---
name: undistort-invertibility-first-slice-contract
description: First-slice contract for SLICE-UI-00 — on-circle injectivity of undistortPoint with zero tangential coefficients
metadata:
  type: reference
---

# First-Slice Contract — SLICE-UI-00

**Parent task:** `undistort-invertibility`
**Work queue path:** `docs/laps/undistort-invertibility/work-queue.md`
**Selected slice:** SLICE-UI-00 — On-circle injectivity, zero tangential
**Status:** Ready for implementation (pending user authorization)

---

## Proof Engineering Level

Proving a fixed theorem — no new definitions needed.

---

## Slice Objective

Prove that `undistortPoint k p ε₁ h₁ = undistortPoint k p ε₂ h₂` implies `ε₁ = ε₂`
when `p.p1 = p.p2 = 0`, `sensorRadius ε₁ = sensorRadius ε₂`, and
`radialTerm k (sensorRadius ε₁) h₁ ≠ 0`.

---

## Included Work

- Create `openlensio_semantics/InjectivityModel.lean` with one theorem:
  `undistortPoint_injective_zero_tangential`
- Add `InjectivityModel` target to `lakefile.toml`
- Run `lake env lean openlensio_semantics/InjectivityModel.lean` and record result
- Create `proof-plan.md` (Stop 2) before writing any tactics
- Create `proof-run-log.md` during execution (Stop 3)
- Create `proof-review.md` (Stop 4)

---

## Excluded Work

- Defining a forward distortion function D
- Any theorem without `hSameR` restriction (SLICE-UI-01)
- Any theorem with nonzero tangential (SLICE-UI-03)
- Any change to existing Lean files other than `lakefile.toml`
- Any entry to `DistortionModel.lean`, `RadialPolynomial.lean`, or `CoordinateTypes.lean`

---

## Allowed Definitions and Theorem Shapes

**Definitions:** None. SLICE-UI-00 uses existing definitions only.

**Theorem shape:** implication — from a conjunction of hypotheses, conclude `ε₁ = ε₂`.

**New helper lemmas allowed:** At most one unnamed `have` for the radial term equality
step (not a new named lemma unless the equality needs significant proof effort).

---

## Load-Bearing Definitions

| Definition | Intended meaning | Invariants in type | Deferred invariants | Downstream risk |
|---|---|---|---|---|
| `undistortPoint k p ε h` | Brown-Conrady U(ε) | None | denominatorNonzero as explicit h | Changes here invalidate all downstream theorems |
| `radialTerm k r h` | R(r) — ignores h in body | None | denominatorNonzero as explicit h | Critical: body-ignores-h is used in proof |
| `denominatorNonzero k r` | Domain predicate for R | None | — | Must remain a Prop (proof-irrelevant) |
| `sensorRadius p` | r = √(x² + y²) | Non-negative (not encoded) | sensorRadius_nonneg lemma | Used in radialTerm arguments |

---

## Ambiguities to Resolve Before Implementation

| Ambiguity | Why it matters | Resolution |
|---|---|---|
| AMB-UI-001 | Gates full invertibility — but UI-00 is injectivity only | Resolved for UI-00: theorem is explicitly scoped to injectivity |
| AMB-UI-002 | Scope of injectivity | Resolved for UI-00: on-circle only, `hSameR` enforced |
| AMB-UI-003 | R ≠ 0 condition | Resolved for UI-00: `hR` is an explicit caller precondition |

No unresolved ambiguity blocks UI-00.

---

## Comment/Formal Alignment Rule

The new file's header must state clearly:
- This proves injectivity on circles (same radius), not global injectivity
- This requires zero tangential coefficients and nonzero radial factor
- This is the first step in the invertibility campaign; it does not prove full invertibility

The theorem name `undistortPoint_injective_zero_tangential` must accurately describe what
it proves. It must NOT be named `undistortPoint_injective` (too broad) or
`undistortPoint_invertible` (wrong claim).

---

## Raw vs. Semantic Layer

All types in this slice are semantic:
- `SensorPoint` — semantic coordinate type
- `RadialCoefficients`, `TangentialCoefficients` — semantic coefficient types
- `denominatorNonzero` — semantic domain predicate
- No raw JSON or parser types appear

---

## Automation Budget

| Tactic | Budget | Notes |
|---|---|---|
| `simp only [...]` | 2 calls | One to unfold undistortPoint/X/Y, one for radialTerm |
| `congr_arg` | 2 calls | Extract x and y components from hU |
| `mul_left_cancel₀` | 2 calls | Cancel R from both sides of hX and hY |
| `SensorPoint.ext` | 1 call | Final step: x and y equalities → point equality |
| `rw` | 1–2 calls | Rewrite hRR into hX and hY |
| Other | 0 | If more tactics needed, emit PROOF STOP |

---

## File Policy

- **Create new file:** yes — `openlensio_semantics/InjectivityModel.lean`
- **Edit existing file:** yes — `lakefile.toml` (add `InjectivityModel` target only)
- **Compatibility re-export needed:** no
- **Why this is a module boundary:** Injectivity theorems are a new semantic family
  separate from the definition + basic identity family in `DistortionModel.lean`.
  The file has a single semantic responsibility: injectivity properties of `undistortPoint`.
- **Files explicitly forbidden:** `DistortionModel.lean`, `RadialPolynomial.lean`,
  `CoordinateTypes.lean`, `LensSemantics.lean`, `ProjectionModel.lean`

---

## Stop Conditions

1. Proof of any subgoal fails twice without progress — emit `PROOF STOP`
2. Any algebra step requires more than 2 `rw` steps — emit `ALGEBRA STOP`
3. Slice expands to touch any excluded file — stop and report
4. Proof requires adding a `simp` lemma to an existing definition — stop and report
5. Any hypothesis appears to make the theorem suspiciously easy — emit `PROOF STOP` with vacuity check

---

## Lean Check Requirements

Narrowest check: `lake env lean openlensio_semantics/InjectivityModel.lean`

This check is sufficient because:
- The new file imports only `DistortionModel`, which is already verified
- No inter-file dependencies are introduced by the theorem itself

Broader check `lake build` is not required for this slice unless imports change.

---

## Completion Conditions

- [ ] `InjectivityModel.lean` compiles with `lake env lean` — exit 0
- [ ] No `sorry`, no linter warnings, no unexpected generated files
- [ ] `undistortPoint_injective_zero_tangential` is the only new declaration
- [ ] `proof-plan.md` created before any tactics written
- [ ] `proof-run-log.md` updated during execution
- [ ] `proof-review.md` created after compilation
- [ ] `work-queue.md` updated: SLICE-UI-00 marked complete
- [ ] SLICE CHECKPOINT emitted before any work on UI-01
