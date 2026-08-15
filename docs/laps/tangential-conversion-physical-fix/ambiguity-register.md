---
name: tangential-conversion-physical-fix-ambiguity-register
description: Open questions and statement-shape decisions for the tangential physical-conversion investigation
metadata:
  type: project
---

# Ambiguity Register — Tangential Conversion Physical-Semantics Fix

## AMB-TCF-001: Conclusion shape of the corrected pipeline theorem

**Issue**: The user asked for "a corrected version of
`opencv_openlensio_full_pipeline_pixel_iff` with the `hq1`/`hq2` hypotheses
swapped ... and determine what the residual condition becomes." A literal
reading could mean: keep the `↔ ws/w = fx` conclusion shape and just swap the
hypotheses, then see if it still proves.

**Resolution**: Hand-derivation (recorded in `proof-capsule.md`) shows that
under the corrected hypotheses, pixel agreement holds *unconditionally* — the
`(fx - ws/w) · T_cv(x',y')` gap term that drives the baseline theorem's →
direction becomes identically zero regardless of `ws/w` vs `fx`, because the
extra F factor exactly cancels it. Concretely, with `q1=p1/F, q2=p2/F` the OTI
tangential term becomes `F·T_cv`, and `(ws/w)·F = fx` always (from `hF_eq`),
so the OTI pixel output equals `fx·T_cv + …` regardless of whether `ws/w`
separately equals `fx`.

This means the naive `pixel_eq ↔ ws/w = fx` statement, ported verbatim under
the corrected hypotheses, is **false** — not "harder to prove," but false, with
an explicit counterexample: pick `fx=1, ws=2, w=1` (so `ws/w=2 ≠ fx=1`) with
`F = (w/ws)·fx = 0.5`, `p1=1, p2=0`, `q1=p1/F=2`, and all radial coefficients
zero. `opencv_openlensio_full_pipeline_pixel_corrected` proves pixel agreement
holds for these values regardless, directly falsifying `pixel_eq → ws/w=fx`.

**Decision** (per Statement Change Protocol — smallest change that avoids
proving a false theorem): state the corrected pipeline result as a plain
universal equality (`∀ x' y', pixel_eq`), not an iff, and add a separate
existential counterexample theorem
(`physical_pixel_agreement_scale_independent_example`) that mechanically
confirms `ws/w = fx` is no longer required. This directly answers "what does
the residual condition become" — it answers "trivially true / no condition
at all" through a proof, and separately refutes the naive iff analog through a
counterexample, rather than asserting a False lemma or silently weakening the
claim. This satisfies the user's explicit ask ("confirm whether it collapses
to something trivially true ... rather than ws/w = fx") without either (a)
attempting to prove a false iff, or (b) silently changing what was asked for
without flagging it.

**Status**: Resolved by proof, not by assumption — see `proof-run-log.md` for
the compiled result. No further user input needed unless the compiled proof
disagrees with this hand-derivation, in which case: STOP and re-open this
item rather than reshaping the theorem again (two-reversal rule).

## AMB-TCF-002: Does `hF_pos : 0 < F` remain necessary?

**Issue**: The baseline `opencv_openlensio_full_pipeline_pixel_sufficiency`
takes `hF_pos : 0 < F` as a hypothesis but its tactic proof does not appear to
use it (grep of the proof body shows no reference to `hF_pos`). Should the
corrected pipeline theorem keep this hypothesis for signature parity, or drop
it as genuinely unused?

**Decision**: Keep it for signature parity with the theorem family (same
argument list shape eases comparison and future composition with the existing
`opencv_openlensio_full_pipeline_pixel_iff`), unless Lean's unused-variable
linter flags it as a warning during Stop 3 compilation, in which case
downgrade to recording it as intentionally-unused-for-parity in
`proof-run-log.md` rather than removing it (removing it would be a signature
change beyond the scope authorized: "hq1/hq2 hypotheses swapped").

**Status**: Deferred to Stop 3 diagnostics check.
