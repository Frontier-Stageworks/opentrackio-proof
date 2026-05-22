---
name: opencv-openlensio-pipeline-equivalence-proof-review-pe04b
description: LAPS Stop 4 proof review for SLICE-PE-04b and SLICE-PE-04c
metadata:
  type: project
---

# Proof Review — PE-04b / PE-04c: Forward Direction of pixel_iff

## Kernel Status

`lake build PipelineEquivalence` — 3298 jobs, build completed successfully (2026-05-22).
No `sorry`, no `admit`, no `axiom` introduced.
Exit code 0. Warnings only (unused variables in earlier lemmas, one unused simp arg).

## Forbidden Constructs

- `sorry`: absent
- `admit`: absent
- unauthorized `axiom`: absent
- `unsafe` / `partial`: absent
- heartbeat limit changes: none
- `field_simp` or `ring_nf` on the full pixel equation: none (applied only to small helper goals)

## Statement Unchanged

`opencv_openlensio_full_pipeline_pixel_iff` theorem statement: identical to frozen form in
proof-capsule-pe04b.md. Parameters, hypotheses, conclusion, and iff direction unchanged.

## Load-Bearing Definition Alignment

All five helper lemmas in `Pipeline/PixelIffHelpers.lean` are unchanged in statement:

| Lemma | Role | Status |
|---|---|---|
| `radial_ratio_scaled_eq` | OTI radial at (F*x,F*y) = CV radial at (x,y) * F | Unchanged |
| `tangential_scaled_eq` | OTI tangential sum = CV tangential sum | Unchanged |
| `principal_offset_cancels` | (ws/w)*ΔPx + ws/2 = cx | Unchanged |
| `tangential_gap_forces_scale` | (fx-ws/w)*T=0 for all x,y + p nonzero → ws/w=fx | Unchanged |
| `pixel_eq_implies_tangential_gap` | New lemma, statement from proof-capsule | As planned |

## Semantic Match to Intent

The theorem states: given all parameter conversions (l_i = k_i/F^(2n), q_i = p_i/F^2,
F = (w/ws)*fx, ΔPx = (w/ws)*(cx-ws/2)) and p1≠0∨p2≠0, the pixel x-outputs agree for
every normalised input iff ws/w = fx.

The → direction correctly extracts ws/w = fx from universal pixel equality by:
1. `pixel_eq_implies_tangential_gap`: rewrites both OTI radial and tangential terms in
   `hspec` to their CV equivalents, then uses `linear_combination` to isolate
   `(fx - ws/w) * T(x',y') = 0` for all x', y'.
2. `tangential_gap_forces_scale`: specializes at (1,1) and (1,-1) for p1≠0, or (0,1)
   for p2≠0, to extract the scalar equality.

This matches the paper's claim: ws/w = fx is the exact additional condition beyond
coefficient conversions for pixel-level agreement.

## Hypothesis Justification

`hp : p1 ≠ 0 ∨ p2 ≠ 0` — required for the → direction. Without at least one nonzero
tangential coefficient, the tangential term T is identically zero and universal pixel
equality holds trivially without implying ws/w = fx. The hypothesis is load-bearing and
non-vacuous.

## Hard Step Identified

The hard step was `rw [h_tang] at hspec`: the sum `A+B` (OTI tangential terms) is not a
contiguous subterm in the left-associative 4-term sum `((C+A)+B)+D` in `hspec`. The fix —
splitting into individual rewrites `h_tang1` and `h_tang2` — was identified by inspecting
the exact Lean error message and reasoning about associativity. Each individual term IS a
contiguous subterm at its nesting level.

## Anti-Pattern Scan

- No broad automation hiding the hard step: the `linear_combination` expression is explicit.
- No proxy property: the theorem directly states and proves ws/w = fx extraction.
- No vacuous hypothesis: `hp` is non-trivially used in `tangential_gap_forces_scale`.
- No unauthorized definition changes.
- No import creep: no new imports added beyond what was already present.
- No `field_simp` on the full hspec: only applied to small 1-or-2-variable subgoals.
- The `linear_combination` residual is 0 by ring (verified in proof-plan-pe04b.md).

## Warnings (Non-Blocking)

- Unused variable `hden` in `radial_ratio_scaled_eq` (pre-existing, not introduced here)
- Unused variables `hw`, `hws` in `tangential_gap_forces_scale` (pre-existing)
- Unused simp arg `add_zero` in `tangential_gap_forces_scale` p2 branch (pre-existing)

These are in earlier lemmas and do not affect correctness. They may be cleaned up in a
separate refactor slice.

## Conclusion

LAPS Stop 4 passed. The theorem `opencv_openlensio_full_pipeline_pixel_iff` is fully proved,
no sorry remains, the proof is kernel-checked, the hard step is explicit, the statement
matches the paper's central claim, and no forbidden constructs are present.
