---
name: bounded-inverse-approximation-ambiguity-register
description: Vector-representation choice, buffer-hypothesis design decision, and the composition-identity sign correction for the bounded-inverse-approximation task
metadata:
  type: project
---

# Ambiguity Register — Bounded Inverse Approximation

## AMB-BIA-001: Vector-space representation

**Issue**: The user explicitly asked to choose between `ℝ × ℝ` or
`EuclideanSpace ℝ (Fin 2)`, "whichever composes more cleanly," checking
`DistortionModel.lean`'s convention but not forcing a match if it creates
friction, and to record the reasoning here.

**Options considered**:

1. **`SensorPoint`-style bespoke struct** (`{x y : ℝ}`, matching
   `CoordinateTypes.lean`'s actual convention exactly). Rejected: this
   struct has no norm/metric structure at all in the existing codebase —
   `sensorRadius` is a hand-written `Real.sqrt (x²+y²)` function with no
   triangle-inequality or scalar-homogeneity lemmas proved about it anywhere
   in the repo. Adopting it here would require hand-proving triangle
   inequality and `‖t•v‖=|t|‖v‖` from scratch — exactly the kind of
   "reimplementing Mathlib" the Lean-Way Model Pass discourages, for a task
   that is fundamentally about norm estimates.

2. **`EuclideanSpace ℝ (Fin 2)`**. Gives the mathematically correct L2 norm
   with full `InnerProductSpace`/`NormedAddCommGroup` API for free (unlike
   option 3 below). Not chosen: component access requires `Fin 2` indexing
   (`x 0`, `x 1`, or `EuclideanSpace.equiv`/`PiLp` conversions), which is
   real syntactic friction for writing out the five-term polynomial formula
   for `Φ_θ` repeatedly, and is not used anywhere else in this repository
   (`grep -rn "EuclideanSpace"` across all `*.lean` files: zero hits before
   this task).

3. **`ℝ × ℝ`**. Genuinely used elsewhere in this repo for 2D points
   (`ProjectionModel.lean:25`: "Both are ℝ × ℝ records; the alias documents
   the coordinate-space role"). Rejected for THIS task specifically because
   Mathlib's default `NormedAddCommGroup (ℝ × ℝ)` instance is the **sup
   norm** (`‖(a,b)‖ = max ‖a‖ ‖b‖`), not the Euclidean norm — silently using
   `‖·‖` on `ℝ × ℝ` would prove a bound in the WRONG geometry (a sup-norm
   disk, not the Euclidean disk `sensorRadius`-style code elsewhere in this
   repo implicitly means by "‖x‖ ≤ R"). Using `ℝ × ℝ` with a hand-rolled
   Euclidean norm function (bypassing the typeclass) would face the same
   "reimplement triangle inequality by hand" problem as option 1.

4. **`ℂ` — chosen.** `Complex.instNormedField`/`NormedAddCommGroup ℂ` in
   Mathlib already carries the *correct* Euclidean norm
   (`‖z‖ = Real.sqrt (z.re²+z.im²)`, verified via `Complex.sq_norm` +
   `Complex.normSq_apply` during scratch-testing), giving triangle
   inequality (`norm_add_le`, `norm_sub_le`), reverse triangle
   (`norm_sub_norm_le`), and scalar-multiplication norm (via
   `Complex.real_smul` + `norm_mul` + `simp`) all for free. Component access
   via `.re`/`.im` is at least as ergonomic as a bespoke struct's `.x`/`.y`.
   Mathematically `ℂ ≅ ℝ²` as a real normed vector space, so this is a
   faithful representation of "2D Euclidean vector," not a different
   mathematical object — a standard, well-established Lean idiom for exactly
   this kind of 2D-Euclidean-estimate task.

**Decision**: `ℂ`. Recorded per the user's explicit instruction to note the
choice and reasoning; not forcing a match to `DistortionModel.lean`'s
`SensorPoint` because doing so would create the friction the user
anticipated (reimplementing norm machinery Mathlib already provides). This
module does not need to interoperate with `SensorPoint` at all — it is
explicitly scoped to be independent of `openlensio_semantics/` and
`opencv_opentrackio_proofs/` (no imports from either).

**Status**: Resolved before any Lean code was written; verified feasible via
scratch `exact?`/direct-lemma checks against this exact Mathlib version
(recorded in `proof-capsule.md`), not merely assumed.

## AMB-BIA-002: How to close the disk-containment gap for `D_t(x)`

**Issue**: see `statement-audit.md` "Correction 2" for the full derivation of
why `D_t(x)` is not automatically inside the same `R`-disk as `x`.

**Options considered**:

1. **Add an explicit extra hypothesis `‖D θ t x‖ ≤ R`** (a "self-mapping"
   condition) alongside `‖x‖ ≤ R`. Keeps `phi_lipschitz` applied at radius
   `R` cleanly, and is honest about what's needed. Rejected as the *primary*
   design (though mathematically valid) because it is not *derivable* from
   the other hypotheses — a caller would need to separately verify
   `D`-self-mapping for their specific `θ, R, t, x`, which is exactly the
   kind of thing layer 4 (fixed-point existence) would normally supply, and
   pulling in a self-mapping assumption without any of the machinery to
   discharge it made the hypothesis feel unmotivated in isolation.

2. **Evaluate `L` at a larger radius `R' = R + |t|·M(θ,R)`** instead of `R`.
   Requires no extra hypothesis (the disk-containment fact becomes provable
   outright from `‖x‖ ≤ R` alone via triangle inequality), but breaks the
   clean `L θ R · M θ R · t²` conclusion shape the user explicitly asked
   for — the final bound would read `L θ (R + |t|·M θ R) · M θ R · t²`,
   which is honest and provable but textually more complex than requested,
   and makes `L`'s *effective* radius argument silently depend on `t`
   (defeating the point of `L` being "explicit in terms of θ and R" as a
   standalone quantity).

3. **Chosen: strengthen `‖x‖ ≤ R` to `‖x‖ + |t|·M(θ,R) ≤ R`.** Makes
   `‖D θ t x‖ ≤ R` a *derived* one-line consequence (via `phi_bounded` at
   `x` + triangle inequality), keeps `L θ R`, `M θ R` exactly as requested,
   and is self-contained (no separate self-mapping proof obligation pushed
   onto the caller — it follows mechanically from the stated hypothesis).
   The "cost" is that `x` lives in a slightly smaller disk than `R` — a
   standard, well-motivated "radius of validity" / buffer-margin condition
   in perturbation analysis, not an ad hoc weakening. Chosen as the cleanest
   option that (a) matches the requested conclusion shape exactly, (b)
   introduces no unprovable/unmotivated extra hypothesis, and (c) is
   honestly documented as a buffer condition rather than silently smuggled
   in as if it were just "‖x‖ ≤ R" restated.

**Decision**: option 3. This is a genuine "smallest statement clarification"
under LAPS's Statement Change Protocol — the conclusion shape is unchanged
from the user's request; only the `x`-containment hypothesis is tightened,
with the reason recorded here rather than silently applied. Not treated as
requiring a hard stop for user authorization, since (a) it does not change
theorem *intent* (still "first-order approximate inverse has O(t²) error on
a bounded disk"), (b) the alternative (option 1) is available and equally
valid if the user prefers it later, and (c) proceeding with medium-task
implementation without a blocking re-ask is standard once Stop 1/2 artifacts
record the reasoning, per `/laps-start`'s own procedure for medium tasks.

**Status**: Resolved; will be re-examined in `proof-review.md` after the
Lean proof compiles, to confirm the derivation of `‖D θ t x‖ ≤ R` from the
buffer hypothesis actually goes through as sketched.

## AMB-BIA-003: Composition-identity sign (see statement-audit.md Correction 1)

**Issue**: the user's prompt states `U_t(D_t(x)) - x = -t•(Φ(x)-Φ(x+tΦ(x)))`;
hand-derivation from the given `D_t`/`U_t` definitions gives the negative of
this, `t•(Φ(x)-Φ(x+tΦ(x)))`.

**Decision**: use the algebraically correct sign in the Lean proof (verified
by hand-deriving twice); the discrepancy has zero effect on the final
theorem (norms erase sign) and is not a statement or hypothesis change.
Recorded rather than silently fixed, per LAPS discipline for any correction
to a user-supplied derivation sketch.

**Status**: Resolved; no further action needed unless the Lean `ring`/`module`
proof of the identity reveals a different discrepancy than hand-computed
here, in which case: stop and re-open this item rather than reshaping the
identity a third time (two-reversal rule).
