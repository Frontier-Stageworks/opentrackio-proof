---
name: opencv-openlensio-pipeline-equivalence-work-queue
description: Slice decomposition and status tracking for the pipeline equivalence task
metadata:
  type: project
---

# Work Queue — OpenCV/OpenLensIO Full Pipeline Equivalence

## Slices

### SLICE-PE-00: Infrastructure (lakefile + imports)
- **Status**: NOT STARTED
- **Deliverable**: Add `PipelineEquivalence` lib entry to `lakefile.toml`; create stub file
  `opencv_opentrackio_proofs/PipelineEquivalence.lean` with imports and module header
- **Imports needed**: `DistortionConversion`, `DistortionModel`
- **Gate**: `lake env lean opencv_opentrackio_proofs/PipelineEquivalence.lean` exits clean
- **Dependencies**: None

### SLICE-PE-01: Define undistortOpenCV
- **Status**: NOT STARTED
- **Deliverable**: `undistortXCV`, `undistortYCV`, `undistortPointCV` definitions in
  `PipelineEquivalence.lean`
- **Contract**: See first-slice-contract.md
- **Gate**: File compiles clean; definitions match intended formulas
- **Dependencies**: SLICE-PE-00

### SLICE-PE-02: Prove radial pipeline equivalence
- **Status**: NOT STARTED
- **Deliverable**: `opencv_openlensio_radial_pipeline_eq` theorem
- **Proof strategy**: Unfold both sides; apply `radial_distortion_value_equivalence`;
  reduce to `sensorRadius ⟨F·x, F·y⟩ = F · sensorRadius ε'` (uses `hF_pos`)
- **Expected difficulty**: Low. Follows closely from existing `radial_distortion_value_equivalence`.
- **Gate**: Compiles clean; proof review passes
- **Dependencies**: SLICE-PE-01

### SLICE-PE-03: Prove full pipeline pixel sufficiency (← direction)
- **Status**: NOT STARTED
- **Deliverable**: `opencv_openlensio_full_pipeline_pixel_sufficiency` theorem
- **Proof strategy**: Substitute all conversion hypotheses and `ws/w = fx`;
  reduce to `field_simp` + `ring` closing an algebraic equality
- **Expected difficulty**: Medium. Long substitution chain but mechanical algebra.
- **Gate**: Compiles clean; proof review passes; the specific `ws/w = fx` step is
  identified in the proof (not hidden by automation)
- **Dependencies**: SLICE-PE-01, SLICE-PE-02

### SLICE-PE-04: Prove full pipeline pixel iff (main result)
- **Status**: NOT STARTED
- **Deliverable**: `opencv_openlensio_full_pipeline_pixel_iff` theorem (iff)
- **Proof strategy**:
  - ← direction: apply sufficiency theorem
  - → direction: extract conditions by specialization at chosen (x', y') values;
    use `principal_point_conversion_iff` for F and ΔPx; use `whole_radial_polynomial_iff`
    for radial coefficients; use `whole_tangential_field_iff` for q1, q2; use `hp` for
    ws/w = fx (specialise at x'=1, y'=0 and use `p1 ≠ 0 ∨ p2 ≠ 0`)
- **Expected difficulty**: High. The → direction requires extracting all conditions from a
  universal equality over a composite expression. The algebra for isolating individual
  conditions needs careful specialization.
- **Gate**: Compiles clean; proof review passes; the `ws/w = fx` extraction step is
  explicitly identified; no sorry; semantic review confirms the iff captures the intent
- **Dependencies**: SLICE-PE-03

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
