---
name: opencv-openlensio-pipeline-equivalence-work-queue
description: Slice decomposition and status tracking for the pipeline equivalence task
metadata:
  type: project
---

# Work Queue — OpenCV/OpenLensIO Full Pipeline Equivalence

## Slices

### SLICE-PE-00: Infrastructure (lakefile + imports)
- **Status**: DONE (2026-05-21)
- **Deliverable**: Add `PipelineEquivalence` lib entry to `lakefile.toml`; create stub file
  `opencv_opentrackio_proofs/PipelineEquivalence.lean` with imports and module header
- **Imports needed**: `DistortionConversion`, `DistortionModel`
- **Gate**: `lake env lean opencv_opentrackio_proofs/PipelineEquivalence.lean` exits clean
- **Dependencies**: None

### SLICE-PE-01: Define undistortOpenCV
- **Status**: DONE (2026-05-21) — compiled clean; semantic checks passed
- **Deliverable**: `undistortXCV`, `undistortYCV`, `undistortPointCV` definitions in
  `PipelineEquivalence.lean`
- **Contract**: See first-slice-contract.md
- **Gate**: File compiles clean; definitions match intended formulas
- **Dependencies**: SLICE-PE-00

### SLICE-PE-02: Prove radial pipeline equivalence
- **Status**: DONE (2026-05-21) — compiled clean; semantic review passed
- **Deliverable**: `opencv_openlensio_radial_pipeline_eq` theorem
- **Proof strategy**: Unfold both sides; apply `radial_distortion_value_equivalence`;
  reduce to `sensorRadius ⟨F·x, F·y⟩ = F · sensorRadius ε'` (uses `hF_pos`)
- **Expected difficulty**: Low. Follows closely from existing `radial_distortion_value_equivalence`.
- **Gate**: Compiles clean; proof review passes
- **Dependencies**: SLICE-PE-01

### SLICE-PE-03: Prove full pipeline pixel sufficiency (← direction)
- **Status**: DONE (2026-05-21) — compiled clean (unused-variable warning for `hF_pos` only)
- **Deliverable**: `opencv_openlensio_full_pipeline_pixel_sufficiency` theorem
- **Proof strategy**: Derive `hws_eq : ws = w * fx` and `hfx : fx ≠ 0` from `hscale`;
  prove radial num/den equalities; rewrite with `hF_eq, hws_eq` (eliminates `ws` and `F`);
  close with `field_simp [hw, hfx, hden_xy]; ring`
- **Key fix**: the `ws/w = fx` step is explicit via `hws_eq` derivation (not hidden);
  avoiding `rw [hscale]` before `field_simp` prevents spurious `fx⁻¹` introduction
- **Gate**: Compiles clean; proof review passes; the specific `ws/w = fx` step is
  identified in the proof (not hidden by automation)
- **Dependencies**: SLICE-PE-01, SLICE-PE-02

### SLICE-PE-04a: Prove ← direction of pixel iff
- **Status**: DONE (2026-05-21) — compiles clean (sorry warning only for → direction)
- **Deliverable**: `opencv_openlensio_full_pipeline_pixel_iff` with ← direction proved
  (→ direction as `sorry` placeholder until PE-04c)
- **Proof strategy**: `constructor; · intro h; exact opencv_openlensio_full_pipeline_pixel_sufficiency ...`
- **Expected difficulty**: Trivial.
- **Gate**: Compiles clean with sorry only in → branch
- **Dependencies**: SLICE-PE-03

### SLICE-PE-04b: Helper lemma — pixel equality implies tangential gap = 0
- **Status**: DONE (2026-05-22)
- **Deliverable**: `pixel_eq_implies_tangential_gap` lemma in `Pipeline/PixelIffHelpers.lean`.
  Given all conversion hypotheses and `h : ∀ x' y', CV = OTI`, proves
  `∀ x' y', (fx - ws/w) * T(x',y') = 0`.
- **Key technical point**: `rw [h_tang]` fails due to associativity — `A+B` is not a
  contiguous subterm in `((C+A)+B)+D`. Fix: split into `h_tang1` and `h_tang2` and
  rewrite individual terms. `field_simp [hF2]` closes each individual component goal.
- **Gate**: `lake build PipelineEquivalence` — no errors.
- **Dependencies**: SLICE-PE-03

### SLICE-PE-04c: Close the iff using PE-04b
- **Status**: DONE (2026-05-22)
- **Deliverable**: `opencv_openlensio_full_pipeline_pixel_iff` in `Pipeline/PixelIff.lean`
  — sorry removed; → direction proved via
  `tangential_gap_forces_scale (pixel_eq_implies_tangential_gap ...)`.
- **Gate**: `lake build PipelineEquivalence` — 3298 jobs, no errors, no sorry.
- **Dependencies**: SLICE-PE-04a, SLICE-PE-04b

## Checkpoint protocol

- Update status after each slice compiles and passes proof review
- Do NOT start the next slice until current slice status = DONE and artifacts updated
- If any slice fails to compile within 3 tactic attempts at a subgoal, stop and emit
  a PROOF STOP with the current goal shape

## Deferred work (out of scope for this task)

- 2D version of the full pipeline iff (both x and y components)
- Theorem for the ΔC (distortion centre) generalisation
- Formal statement of the "pure radial lens" special case (p1 = p2 = 0)
- OpenCV `undistortPoints` iterative vs. closed-form comparison
