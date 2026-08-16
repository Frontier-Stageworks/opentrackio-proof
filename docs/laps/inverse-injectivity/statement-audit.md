---
name: inverse-injectivity-statement-audit
description: Audit of D_eq_implies_eq, inverse_step_maps_disk, inverse_step_lipschitz against user intent, and the scope boundary against layer-4 existence
metadata:
  type: project
---

# Statement Audit — Inverse Injectivity

## `D_eq_implies_eq`

Matches user intent exactly: standard "contraction map is injective"
argument, specialized to `D θ t`. Hypotheses are all necessary — `hR`,
`ha`, `hb` establish the domain; `hcontract` is the load-bearing
non-degeneracy condition (without it, `D θ t` need not be injective — e.g.
`t = 0` gives `D θ 0 = id`, trivially injective, but for `t` large enough
that `|t|·L θ R ≥ 1` there is no general guarantee, matching the intuition
that a "distortion strength" too large relative to its own Lipschitz bound
can fold the disk onto itself non-injectively).

## `D_injective_on_disk`

Genuinely thin corollary — `Set.InjOn`'s definition unfolds to exactly
`D_eq_implies_eq`'s hypothesis/conclusion shape once the membership
predicates are unpacked, confirmed to compose with zero friction during
scratch-testing (see proof-capsule.md). Included per the user's own
stated preference ("if it composes cleanly ... include it").

## `inverse_step_maps_disk`, `inverse_step_lipschitz`

Both are direct restatements of facts already load-bearing inside the
existing `inverse_approx_error` proof (which computes `‖D θ t x‖ ≤ R` and
implicitly uses the Lipschitz bound on the tangential map), now extracted
as standalone, reusable theorems about the map `T_y(z) = y - t•Φ θ z`
specifically because a Banach argument needs them stated about the
*iteration map*, not about a single point's image. No new estimate is
proved — both reduce to `phi_bounded`/`phi_lipschitz` directly, exactly as
the user specified ("no new estimates needed").

## Scope boundary: what is and is NOT established

**Established by this task**: `D θ t` is injective on the disk (given the
contraction condition), and the two properties (self-mapping + contraction)
that a Banach fixed-point argument about `T_y` would need as hypotheses.

**NOT established**: that `T_y` (or `D θ t`) actually *has* a fixed point /
inverse. `inverse_step_maps_disk` + `inverse_step_lipschitz` are exactly
the two premises `ContractingWith`/Banach fixed-point theorems require, but
supplying them to Mathlib's fixed-point machinery, wiring up the
`CompleteSpace` instance on the closed disk (as a subtype or via
`Metric.closedBall`), and extracting existence/uniqueness of the fixed
point is a distinct, larger piece of work — explicitly deferred, not
attempted, and not even sketched here. Every doc-comment added in this
task says this explicitly (per the user's requirement (a)).

This distinction is the entire point of splitting this into two tasks, and
is the main thing this statement audit needs to get right: it would be a
real overclaim to describe `inverse_step_maps_disk`/`inverse_step_lipschitz`
as "proving `D` is invertible" — they are necessary but not sufficient
prerequisites, and are documented as such everywhere they appear.

## Vacuity check

- `D_eq_implies_eq`: `hcontract : |t|·L θ R < 1` is satisfiable for any
  `θ, R` by choosing `t` small enough (e.g. `t = 0` always satisfies it
  when `L θ R ≥ 0`, which it always is) — not vacuous.
- `inverse_step_maps_disk`: `hy` is the same buffer condition already
  shown non-vacuous in `docs/laps/bounded-inverse-approximation/statement-audit.md`.
- `inverse_step_lipschitz`: no hypothesis beyond disk membership; not vacuous.
