---
name: inverse-existence-ambiguity-register
description: Choice of exists_fixedPoint' over a bundled-subtype ContractingWith.fixedPoint approach, and how uniqueness is obtained
metadata:
  type: project
---

# Ambiguity Register — Local Existence and Uniqueness

## AMB-IE-001: `ContractingWith.exists_fixedPoint'` (set-based) vs. a bundled subtype + `ContractingWith.fixedPoint`

**Issue**: the user's proof approach sketch suggested "package the closed
disk as a complete metric subtype... lift `inverseStep θ t y` to a
self-map of that subtype... invoke the fixed-point existence/uniqueness
result." This describes the *general shape* correctly but leaves open
which of Mathlib's two fixed-point entry points to use:

1. Fully bundle the disk as a subtype `↥{z : ℂ // ‖z‖ ≤ R}`, define the
   self-map `g : ↥s → ↥s` by hand, get `[CompleteSpace ↥s]` via
   `IsClosed.completeSpace_coe` (an *instance*, needs the closedness proof
   registered via `haveI`), then use `ContractingWith.fixedPoint`
   (`[Nonempty α] [CompleteSpace α]` version, `namespace ContractingWith`,
   `MetricSpace α` section).
2. Use `ContractingWith.exists_fixedPoint'` directly on the *set* `s : Set
   ℂ` (not a bundled subtype), which internally handles the
   subtype-restriction (`hsf.restrict f s s`) itself — the caller only
   supplies `IsComplete s` (from `IsClosed.isComplete`, a plain `Prop`, no
   instance-resolution needed) and `MapsTo f s s`.

**Decision**: option 2 (`exists_fixedPoint'`). Confirmed via scratch-testing
(see proof-plan.md) that it compiles end-to-end with minimal friction — the
only subtype-level reasoning needed is inside the one `LipschitzWith`
`have`, which is short and mechanical (`Subtype.dist_eq` + the existing
`inverse_step_lipschitz` fact). Option 1 would additionally require
manually defining the subtype-valued self-map and registering the
`IsClosed`-as-instance step for `CompleteSpace` typeclass resolution —
strictly more subtype bookkeeping for the same result. This is exactly the
kind of choice the user's proof sketch left open ("check ... before
building anything by hand"); resolved by testing both shapes' entry costs
rather than guessing.

**Status**: resolved before writing any code in the real file, via a
passing scratch test.

## AMB-IE-002: source of the uniqueness clause

**Issue**: the user offered two options — "take it directly from the
Banach result or cross-check it against `D_eq_implies_eq`, whichever is
cleaner."

**Decision**: take it directly from the Banach result, via
`ContractingWith.fixedPoint_unique'` (applied to the two subtype-packaged
fixed points `⟨z, hzs⟩`, `⟨w, hws⟩` of the *restricted* map, then
`Subtype.ext`/`congrArg Subtype.val` to descend back to `z = w` in `ℂ`).
Confirmed to compile in the scratch test. `D_eq_implies_eq` is not invoked
in the final proof — it remains available (and is not contradicted; it
proves the same fact by a different, more elementary route not requiring
completeness machinery at all) but including both would be redundant, not
"cleaner." Not treated as leaving `D_eq_implies_eq` unused/dead code: it is
still a standalone, independently useful theorem (e.g. usable without
pulling in Mathlib's fixed-point machinery at all), documented as such in
its own file section.

**Status**: resolved; if Stop 3 finds the `fixedPoint_unique'` route hits
friction beyond the time-box, the fallback (cross-check via
`D_eq_implies_eq`, which needs no completeness/subtype machinery at all —
just plug both `z` and `w` into `D_eq_implies_eq`'s hypotheses once
`D θ t z = y = D θ t w` is established) is recorded here as the documented
alternative, not something to discover fresh under time pressure.
