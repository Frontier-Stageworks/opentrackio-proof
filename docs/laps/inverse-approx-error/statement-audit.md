---
name: inverse-approx-error-statement-audit
description: Full hand-derivation of inverse_approx_error_vs_preimage's bound, confirming the weakest-hypothesis claim and the prescribed derivation chain
metadata:
  type: project
---

# Statement Audit — Approximate-Inverse Error Relative to a True Preimage

## Full derivation (verified by hand before any Lean code)

Notation: `e := ‖U θ t y - z‖`, `q := |t| * L θ R`.

**Step 1** — from `hDz : D θ t z = y`, i.e. `z + t•Φθz = y`:
`inverseStep θ t y z = y - t•Φθz = (z + t•Φθz) - t•Φθz = z`. So
`z = inverseStep θ t y z`.

**Step 2** — `U θ t y = y - t•Φθy = inverseStep θ t y y`, definitionally
(both `unfold` to the identical expression).

**Step 3** — `inverse_step_lipschitz θ R t hR y y z hy hz` (note: BOTH
disk-membership arguments are `hy`/`hz`, exactly the hypotheses given, no
strengthening needed) gives
`‖inverseStep θ t y y - inverseStep θ t y z‖ ≤ q·‖y-z‖`, i.e. (via steps
1–2) `e ≤ q·‖y-z‖`. **(A)**

**Step 4** — `‖y-z‖ = ‖D θ t z - z‖ = ‖t•Φθz‖ = |t|·‖Φθz‖ ≤ |t|·M θ R` via
`phi_bounded θ R hR z hz` (uses `hz`, not `hy`). **(tight route only needs
this — see "finding" below.)**

**Step 5 (the user's prescribed route, not the tight shortcut)**:
- `‖y - U θ t y‖ = ‖y - (y - t•Φθy)‖ = ‖t•Φθy‖ = |t|·‖Φθy‖ ≤ |t|·M θ R` via
  `phi_bounded θ R hR y hy` (uses `hy` — this is exactly why the weaker
  `‖y‖ ≤ R` suffices and the buffer condition is not needed: `phi_bounded`
  only ever needs a disk-membership fact for the *specific point* it's
  applied at, and here that point is `y` itself, already given directly by
  `hy`). Call this **(C)**.
- Triangle inequality: `‖y-z‖ ≤ ‖y - U θ t y‖ + ‖U θ t y - z‖ = ‖y-U θ t y‖ + e`.
  Combined with (C): `‖y-z‖ ≤ |t|·M θ R + e`. **(D)**
- Combine (A) and (D): `e ≤ q·(|t|·M θ R + e) = q·|t|·M θ R + q·e`
  (multiplying (D) by `q ≥ 0` — needs `L θ R ≥ 0`, hence `hR`, to know
  `q = |t|·L θ R ≥ 0`).
- Rearrange: `e - q·e ≤ q·|t|·M θ R`, i.e.
  `(1-q)·e ≤ q·|t|·M θ R = |t|·(|t|·L θ R·M θ R)` — **matches the user's
  stated intermediate inequality exactly**,
  `(1 - |t|*L θ R) * e ≤ |t| * (|t| * L θ R * M θ R)`.
- `0 < 1-q` from `hcontract : q < 1` (explicit `have`).
- Divide: `e ≤ (|t|·(|t|·L θ R·M θ R)) / (1-q) = (|t|² · L θ R · M θ R) / (1-q)`
  — **exactly the target.**

## Confirmed: `‖y‖ ≤ R` (not the buffer condition) suffices

`phi_bounded` is applied at `y` in step (C) purely to bound `‖Φ θ y‖`,
which needs only `‖y‖ ≤ R` — never a bound on `‖D θ t y‖` or any other
derived point. The buffer condition `‖y‖ + |t|*M θ R ≤ R` (used elsewhere
in the file, e.g. `inverse_step_maps_disk`, `D_exists_unique_preimage`)
exists specifically to guarantee `D`/`inverseStep`'s *output* also lands in
the disk (a self-mapping property) — a property this theorem never needs,
because it never applies `inverse_step_lipschitz`/`phi_bounded` to a point
constructed as `inverseStep θ t y (something)`; the only points involved
are `y` and `z` themselves, both given directly as `≤ R` by hypothesis.
**Confirmed: the user's instinct to use the weaker hypothesis was correct;
no substitution needed.**

## Finding: steps 1–4 alone give a tighter, denominator-free bound

`e ≤ q·‖y-z‖ ≤ q·(|t|·M θ R) = |t|²·L θ R·M θ R`, using only (A) and step
4 — no triangle inequality, no `hcontract`. Since `0 < 1-q < 1`,
`|t|²·L θ R·M θ R ≤ (|t|²·L θ R·M θ R)/(1-q)` (dividing a nonnegative
quantity by a number in `(0,1)` only increases it), so this tighter bound
implies the stated target. Recorded in `proof-capsule.md` and
`ambiguity-register.md`; the prescribed (triangle-inequality) derivation is
implemented anyway, per the reasoning there.

## Vacuity / hypothesis-use check for `inverse_approx_error_vs_preimage`

| Hypothesis | Used in the prescribed (triangle-inequality) proof? | Used in the tighter shortcut? |
|---|---:|---:|
| `hR` | yes (`L θ R ≥ 0` for step 5's multiply-by-`q`) | no |
| `hcontract` | yes (`1-q > 0` for the division) | no |
| `hy` | yes (step C, `phi_bounded` at `y`) | no |
| `hz` | yes (step 4, `phi_bounded` at `z`) | yes |
| `hDz` | yes (step 1) | yes |

Every hypothesis is load-bearing in the prescribed proof — not vacuous, not
over-strong. (The shortcut needing fewer hypotheses is exactly the
"tighter bound" finding above, not a sign the stated hypotheses are wrong
for the *stated* theorem — the theorem asks for the standard a priori
bound shape, which legitimately uses all of them.)

## Corollary (`inverse_approx_exists_unique_with_error`) — thinness check

`D_exists_unique_preimage θ R t hR hcontract y hy'` (with `hy'` the buffer
condition, exactly matching the corollary's own `hy` hypothesis) gives
`∃! z, ‖z‖≤R ∧ D θ t z = y`. For that `z`: apply
`inverse_approx_error_vs_preimage θ R t hR hcontract y z hy'' hz hDz`,
where `hy'' : ‖y‖ ≤ R` is derived from the buffer condition `hy'` (same
"drop the nonneg `|t|*M θ R` term" pattern already used identically in
`D_exists_unique_preimage`'s own proof and `inverse_step_maps_disk`'s call
sites throughout the file) — attach the resulting error bound to `z`. For
uniqueness: any `w` satisfying the *first two* conjuncts (`‖w‖≤R ∧
D θ t w = y`) must equal `z` by `D_exists_unique_preimage`'s own
uniqueness clause — the third conjunct (error bound) doesn't need separate
uniqueness reasoning, since it's a *derived consequence* of the first two,
not an independent constraint (any `w` satisfying the first two conjuncts
automatically satisfies the third, by re-applying
`inverse_approx_error_vs_preimage` to `w`). Expected to be a genuinely
short proof — if it isn't, that's the "stop and report" trigger the user
specified.
