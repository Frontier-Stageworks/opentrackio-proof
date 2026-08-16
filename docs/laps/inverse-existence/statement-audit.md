---
name: inverse-existence-statement-audit
description: Audit of D_exists_unique_preimage against user intent and against docs/laps/inverse-injectivity's stated deferral
metadata:
  type: project
---

# Statement Audit — Local Existence and Uniqueness

## Match to user intent

Exact match to the user-specified signature. Plain English: for a
distortion strength `t` small enough relative to the disk radius `R` (the
contraction condition) and a target point `y` in the buffer disk, there is
exactly one point `z` in the disk that `D θ t` maps to `y` — i.e. `D θ t`
has a genuine local inverse on this disk, at this point.

## Relationship to `docs/laps/inverse-injectivity/`

That capsule's own text says: "existence of the true inverse... requires
Mathlib's ContractingWith/CompleteSpace machinery... is a separate,
deferred task, not attempted here." This theorem is exactly that deferred
task, now attempted and (pending Stop 3) completed. No prior theorem
statement is changed — `D_eq_implies_eq`, `inverse_step_maps_disk`,
`inverse_step_lipschitz` are all read-only inputs to this proof.

## Relationship to SQ-CV-07

This theorem is a **standalone mathematical fact about the polynomial
Brown-Conrady model** — it says nothing about OpenCV, OpenTrackIO, units,
or which direction (D→U vs U→D) a real implementation should compute. Per
the user's explicit instruction, the doc update accompanying this theorem
must state this relevance-is-separate framing explicitly, not imply that
proving local invertibility of the abstract model resolves anything about
which JSON `distortion.model` value real producers should emit. The
existence of a true inverse on *some* domain is a necessary but not
sufficient step toward that interoperability question; the update records
that a "rigorous domain" now exists, and nothing more.

## Vacuity check

Same two hypotheses as `inverse_step_maps_disk`/`D_eq_implies_eq`
(`hcontract`, `hy`), already shown non-vacuous in the prior tasks'
statement-audit.md files (`docs/laps/bounded-inverse-approximation/`,
`docs/laps/inverse-injectivity/`). No new hypothesis is introduced by this
theorem — it is a genuine *strengthening* (existence + uniqueness, not just
injectivity) under the *same* hypothesis set as the prerequisites, which is
exactly right: a Banach argument should not need more than what
self-mapping + contraction already provide.
