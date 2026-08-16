---
name: bounded-inverse-approximation-statement-audit
description: Audit of the three theorem statements against the user's intent, including the two corrections made during planning (composition-identity sign, buffer hypothesis)
metadata:
  type: project
---

# Statement Audit — Bounded Inverse Approximation

## `phi_bounded` and `phi_lipschitz`

Direct formalizations of exactly what the user asked: an explicit-in-`(θ,R)`
boundedness estimate and Lipschitz estimate on the disk `‖·‖ ≤ R`. No
ambiguity here beyond the representation choice (see ambiguity-register.md
AMB-BIA-001) and the exact constants (derived in proof-plan.md/algebra-plan.md,
not tight but explicit, matching the user's ask for "an explicit M/L," not
"the sharpest possible M/L").

## `inverse_approx_error` — two corrections made during planning

### Correction 1: composition-identity sign

The user's prompt states the proof should proceed "via the composition
identity `U_t(D_t(x)) - x = -t • (Φ_θ(x) - Φ_θ(x + t • Φ_θ(x)))`." Deriving
this directly from the given definitions `D_t(x) = x + t•Φ_θ(x)` and
`U_t(y) = y - t•Φ_θ(y)`:

```
U_t(D_t(x)) = D_t(x) - t•Φ_θ(D_t(x))
            = x + t•Φ_θ(x) - t•Φ_θ(x + t•Φ_θ(x))
⟹ U_t(D_t(x)) - x = t•(Φ_θ(x) - Φ_θ(x + t•Φ_θ(x)))
```

This is the **negative** of the identity as literally stated in the prompt
(`t•(Φ(x)-Φ(x+tΦ(x)))` vs. the prompt's `-t•(Φ(x)-Φ(x+tΦ(x)))`). Confirmed
by hand-deriving twice independently before writing this note. This does
**not** affect the final theorem, since the conclusion is stated in terms of
a norm (`‖U_t(D_t(x))-x‖`), and `‖v‖ = ‖-v‖` for any `v` — the sign is
invisible after taking the norm. The Lean proof will use the algebraically
correct sign (`t•(Φ(x)-Φ(x+tΦ(x)))`, provable by unfolding `D`/`U` and
`ring`/`module`-normalizing); this is a proof-step correction, not a
theorem-statement change, and does not require stopping for authorization
(no change to any hypothesis, conclusion, or definition — purely an internal
derivation detail the user's prompt got backwards). Recorded here per LAPS
discipline (silent corrections to a user-supplied derivation sketch must be
flagged, not just fixed quietly).

### Correction 2: the disk-containment gap (buffer hypothesis)

The final estimate needs the Lipschitz bound applied to the pair `(x,
D_t(x))`. `phi_lipschitz` only holds for **both** points inside the *same*
disk of radius `R`. `x` is given to be in that disk (that's the theorem's
premise), but `D_t(x) = x + t•Φ_θ(x)` is **not** automatically inside the
same disk — `‖D_t(x)‖ ≤ ‖x‖ + |t|·‖Φ_θ(x)‖ ≤ R + |t|·M(θ,R)`, which exceeds
`R` for any nonzero `t` and nonzero `M`. The user's prompt does not mention
this gap. Left unaddressed, either (a) the theorem as literally stated would
require an unstated/false auxiliary fact to prove (a genuine gap, not
provable as written), or (b) `L` would silently need to be evaluated at a
larger radius `R + |t|·M(θ,R)` rather than `R`, breaking the clean
`L·M·t²` shape the user explicitly asked for.

**Resolution chosen**: strengthen the `x`-containment hypothesis from
`‖x‖ ≤ R` to `‖x‖ + |t|·M(θ,R) ≤ R` (x lives in a "buffer" disk of radius
`R` *minus* the worst-case displacement). This makes `‖D_t(x)‖ ≤ R` a
**derived fact** (provable from the hypothesis via `phi_bounded` + triangle
inequality), not an additional assumed hypothesis, and keeps `L`, `M`
cleanly parametrized by `(θ, R)` alone — exactly matching the user's
requested `L·M·t²` conclusion shape. See `ambiguity-register.md` AMB-BIA-002
for the two alternatives considered and why this one was chosen.

This hypothesis is not vacuous: for any `θ, R` with `R ≥ 0`, it is satisfiable
by any `x` with `‖x‖` small enough relative to `t` (e.g. `x = 0` always
satisfies it when `t = 0`, and more generally whenever `|t| ≤ R / M(θ,R)`
there is room for nonzero `x`). It correctly encodes a genuine "radius of
validity" for the first-order approximation — for `t` too large relative to
`R`, the hypothesis becomes unsatisfiable for any nonzero-displacement `x`,
which is the mathematically correct behavior of a local/perturbative
estimate, not a defect.

## Semantic match to user intent

Both corrections are proof-engineering-level clarifications of an
under-specified sketch, not changes to what the user is asking to be true.
The final `inverse_approx_error` conclusion (`‖U_t(D_t(x)) - x‖ ≤ L θ R · M θ
R · t^2`) is **exactly** the shape requested, with one additional, honest,
non-hidden hypothesis whose necessity is explained above.

## Vacuity check

- `phi_bounded`, `phi_lipschitz`: hypotheses (`0 ≤ R`, `‖z‖ ≤ R`, etc.) are
  standard non-degenerate domain restrictions, not self-implying.
- `inverse_approx_error`: the buffer hypothesis is satisfiable (see above,
  and concretely witnessed for the degenerate case `θ = 0` where `M θ R = 0`
  for all `R`, making the hypothesis reduce to the original `‖x‖ ≤ R`) — not
  vacuous.
