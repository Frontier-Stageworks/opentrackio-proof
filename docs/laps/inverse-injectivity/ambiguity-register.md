---
name: inverse-injectivity-ambiguity-register
description: The inverseStep naming decision and the smul_norm helper promotion for the inverse-injectivity task
metadata:
  type: project
---

# Ambiguity Register — Inverse Injectivity

## AMB-II-001: `inverseStep` named function vs. raw expression

**Issue**: the user's literal signatures for `inverse_step_maps_disk` and
`inverse_step_lipschitz` write out `y - t • Φ θ z` inline, but explicitly
offered the option to introduce a named `inverseStep` function instead, "if
it reads more cleanly," asking for the choice to be noted here if taken.

**Decision**: introduce
`noncomputable def inverseStep (θ : Coeffs) (t : ℝ) (y z : ℂ) : ℂ := y - t • Φ θ z`
and state both theorems in terms of it. Reasoning:

1. The expression `y - t • Φ θ z` appears 4 times across the two theorem
   statements and their proofs (twice per theorem: once for `a`, once for
   `b`, in `inverse_step_lipschitz`); naming it once removes repetition.
2. It gives the fixed-point iteration step a name that will be directly
   reusable if/when the deferred existence task picks this work back up
   (a Banach argument is naturally phrased as "the map `T_y`, defined by
   ..., is a contraction" — `inverseStep` is exactly that `T_y`, pre-named).
3. It does not change what is proved — `inverseStep θ t y z` unfolds
   definitionally to `y - t • Φ θ z`, so any caller can `unfold inverseStep`
   to recover the raw-expression form the user wrote if needed.

Not treated as a statement change requiring a stop: the user pre-authorized
this exact deviation in the prompt.

**Status**: resolved before writing any Lean code.

## AMB-II-002: promoting `smul_norm` to a top-level lemma

**Issue**: `‖t • w‖ = |t| * ‖w‖` is currently only available as a local
`have hsmul_norm` inside `inverse_approx_error`'s proof (not reusable by
other theorems, and that theorem is explicitly not to be touched in this
task).

**Decision**: add a new top-level theorem `smul_norm (t : ℝ) (w : ℂ) :
‖t • w‖ = |t| * ‖w‖`, proved identically to the existing local version
(`rw [Complex.real_smul, norm_mul]; simp`), and use it in all three new
theorems. This is purely additive — `inverse_approx_error`'s own local
`have` is left exactly as it was, not refactored to use the new lemma
(refactoring an existing, already-reviewed proof is out of scope for this
task; the new lemma exists for the new proofs only). A future cleanup task
could have `inverse_approx_error` call the new top-level lemma instead of
its local `have`, but that is a refactor of existing, accepted code and is
not authorized here.

**Status**: resolved; this is a genuine "helper lemma reused ≥2 times"
promotion per LAPS's own guidance, not scope creep — it is directly used by
`D_eq_implies_eq`, `inverse_step_maps_disk`, and `inverse_step_lipschitz`
(3 of the 3 new load-bearing theorems).
