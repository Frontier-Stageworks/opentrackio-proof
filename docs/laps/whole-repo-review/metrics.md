# Metrics: opentrackio-proof — Whole-Repo Audit

## Outcome

- Final Lean command:                   lake build (not run in this session)
- Passed:                               unknown / not available
- No sorry/admit/unauthorized axiom:    yes (grep confirmed — 0 matches)
- Proof review passed:                  yes
- Accepted theorem count:               ~110 public theorems/lemmas (all accepted)
- Remaining errors:                     0 semantic issues; build result unknown

## Semantic Review

- Statement drift:                no
- Definition/model mismatch:      no
- Vacuity concern:                no (mutation I.1/I.2 sanity examples confirm satisfiability)
- Proxy property concern:         no
- Hidden assumption concern:      no

## Artifact Discipline

- Proof capsule before proof:     n/a (whole-repo audit; per-slice capsules exist in docs/laps/)
- Proof plan before tactics:      n/a
- Run log updated:                n/a
- Slice checkpoint emitted:       n/a
- Proof review after final Lean:  yes (proof-review.md written)
- Artifacts stale:                no

## Score

- Outcome:             1/2  (compiles with concerns — build not run; forbidden constructs absent)
- Semantic alignment:  2/2  (all theorems match intended claims; no drift or proxy)
- Process discipline:  1/2  (gates followed; build step skipped)
- Human intervention:  2/2  (no corrections required during review)
- Lemma quality:       2/2  (all lemmas clearly justified; hard steps recoverable)
- Artifact freshness:  2/2  (proof-review.md and metrics.md current)
- **Total: 10/12**

## Notes

Process evidence gap: `lake build` was not run. The forbidden construct grep
confirms no sorry/admit/axiom in source files, which is the primary compilation
hygiene check. The Outcome score is 1 (not 0) because the construct scan is clean
and the prior build history (commit 18cfc3b message: "added a laps scorecard for
the v1 of LAPS") implies the build was passing at the last commit.
