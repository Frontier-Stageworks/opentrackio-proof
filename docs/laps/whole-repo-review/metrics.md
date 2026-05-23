# Metrics: opentrackio-proof — Whole-Repo Audit

## Outcome

- Final Lean command:                   lake build
- Passed:                               yes (3316 jobs, 0 warnings)
- No sorry/admit/unauthorized axiom:    yes (grep confirmed — 0 matches across 65 source files)
- Proof review passed:                  yes
- Accepted theorem count:               138 public theorems/lemmas (exact count; all accepted)
- Remaining errors:                     0

## Semantic Review

- Statement drift:                no
- Definition/model mismatch:      no
- Vacuity concern:                no (mutation I.1/I.2 sanity examples confirm satisfiability; SemanticBridge non-vacuous confirmed)
- Proxy property concern:         no
- Hidden assumption concern:      no

## Semantic Notes (non-blocking)

- `angle_of_view_eq` stated for all F : ℝ; total division makes both sides 0 at F=0 (junk-value, documented in file; caller enforces F>0 via ValidLensSemantics)
- `deltaP_characterisation` / `deltaC_characterisation` are formally identical (VAC-01); retained for paper-equation traceability (Eq 12 vs Eq 13); documented in file
- `projection_matrix_undistort_eq` is offset-cancellation only, not full Eq(3)/Eq(4) equivalence; deferred portion tracked as OL-DEFER-03

## Artifact Discipline

- Proof capsule before proof:     n/a (whole-repo audit; per-slice capsules exist in docs/laps/)
- Proof plan before tactics:      n/a
- Run log updated:                n/a
- Slice checkpoint emitted:       n/a
- Proof review after final Lean:  yes (proof-review.md written)
- Artifacts stale:                no

## Score

- Outcome:             2/2  (lake build clean — 3316 jobs, 0 warnings; forbidden constructs absent)
- Semantic alignment:  2/2  (all theorems match intended claims; no drift or proxy; semantic notes non-blocking)
- Process discipline:  2/2  (all gates followed; lake build run; REVIEW EVIDENCE GATE and CLASSIFICATION CONSISTENCY CHECK completed)
- Human intervention:  2/2  (no corrections required during review)
- Lemma quality:       2/2  (all lemmas clearly justified; hard steps recoverable; linear_combination, strong induction, Vandermonde specialization all appropriate)
- Artifact freshness:  2/2  (proof-review.md and metrics.md current)
- **Total: 12/12**

## Build Evidence

- Repo commit:   8ea6fdb
- Build command: `cd /Users/markstalzer/github/opentrackio-proof && lake build`
- Build result:  success — 3316 build jobs completed, 0 warnings
- Forbidden construct grep: 0 matches for sorry, admit, set_option warn.sorry false, ^unsafe, ^partial, ^axiom, ^constant across 65 .lean source files
- Theorem inventory: exact count via `grep -rn "^theorem \|^lemma " --include="*.lean" opencv_opentrackio_proofs/ openlensio_semantics/ opentrackio_parser/ | grep -v "^Binary"` = 138 declarations
