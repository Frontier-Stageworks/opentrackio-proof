---
name: inverse-approx-error-ambiguity-register
description: The tighter-bound finding for inverse_approx_error_vs_preimage, and the ∃! packaging choice for the corollary
metadata:
  type: project
---

# Ambiguity Register — Approximate-Inverse Error Relative to a True Preimage

## AMB-IAE-001: a tighter, denominator-free bound is available but not used

**Finding**: `inverse_approx_error_vs_preimage`'s hypotheses (specifically,
`hDz : D θ t z = y` being an *exact* equality) support proving the strictly
tighter bound `‖U θ t y - z‖ ≤ |t|² · L θ R · M θ R` directly from
`inverse_step_lipschitz` + `phi_bounded` at `z` alone — no triangle
inequality through `y - U θ t y`, no `hcontract`, no division. This
tighter bound trivially implies the user's stated target (dividing a
nonnegative quantity by `1-q ∈ (0,1)` only increases it). See
`statement-audit.md` for the full derivation of both routes.

**Decision**: implement the user's prescribed derivation (triangle
inequality + rearrangement + division) rather than the shortcut, because:

1. The user wrote out the intermediate inequality
   `(1 - |t|*L θ R) * e ≤ |t| * (|t| * L θ R * M θ R)` explicitly and asked
   specifically for the division step to be scratch-tested — this level of
   detail reads as a deliberate choice of derivation, not an oversight
   that a simpler route would silently correct.
2. The prescribed route is the *general-purpose* Banach a priori estimate
   pattern (it works even when the "known point" is merely close to a
   fixed point, not exactly equal to one) — establishing that pattern here
   has plausible forward-looking value for this module (e.g. if a future
   task needs an error bound from an *approximate* rather than *exact*
   preimage, this is the technique that generalizes; the shortcut does
   not, since its step 1 needs exact equality).
3. Both routes prove the *same theorem statement* — the choice only
   affects proof internals, not the artifact the user asked for.

**Not treated as requiring a stop**: this is a "the proof turned out
easier than expected in one particular way" finding, not a "the stated
hypotheses are insufficient" finding (the opposite of what the user's
explicit stop condition was about) — recorded per the same transparency
principle, not because it blocks progress.

**Status**: resolved; flagged in the final report per the user's general
expectation of transparency about anything found along the way, matching
the spirit (if not the letter) of the stated stop conditions.

## AMB-IAE-002: `∃!` packaging for `inverse_approx_exists_unique_with_error`

**Issue**: the user offered latitude ("Adjust the exact packaging of the
∃! statement if a cleaner formulation emerges... the point is: obtain
existence/uniqueness of z from D_exists_unique_preimage, then apply
inverse_approx_error_vs_preimage to that z").

**Decision**: use the statement exactly as given —
`∃! z : ℂ, ‖z‖ ≤ R ∧ D θ t z = y ∧ ‖U θ t y - z‖ ≤ (...)`. Considered and
rejected alternatives:

- Splitting into a separate existence lemma returning `z` plus a
  standalone error-bound fact: rejected, the user's `∃!` packaging is
  already clean and directly usable, no benefit found to splitting it.
- Weakening to `∃ z, ... ∧ ∀ w, (...) → w = z` (unfolded `ExistsUnique`):
  rejected, `∃!` notation is standard, idiomatic, and Mathlib's own
  `ExistsUnique` machinery (`existsUnique_of_exists_of_unique` or manual
  `⟨z, ⟨...⟩, fun w hw => ...⟩` construction) composes fine with it — no
  packaging friction found during implementation (see proof-run-log.md).

**Status**: resolved; no cleaner formulation emerged, used as given.
