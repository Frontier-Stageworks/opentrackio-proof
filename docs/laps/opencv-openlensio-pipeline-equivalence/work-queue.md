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
- **Status**: NOT STARTED
- **Deliverable**: `opencv_openlensio_full_pipeline_pixel_iff` with ← direction proved
  (→ direction as `sorry` placeholder until PE-04c)
- **Proof strategy**: `constructor; · intro h; exact opencv_openlensio_full_pipeline_pixel_sufficiency ...`
- **Expected difficulty**: Trivial.
- **Gate**: Compiles clean with sorry only in → branch
- **Dependencies**: SLICE-PE-03

### SLICE-PE-04b: Helper lemma — pixel equality implies ws/w = fx
- **Status**: NOT STARTED
- **Deliverable**: `pixel_eq_implies_scale` (or inline `have`) — given all coefficient
  conditions and F, ΔPx conditions, the pixel equality for all (x', y') implies ws/w = fx
- **Theorem statement**: See statement note below. Uses `hp : p1 ≠ 0 ∨ p2 ≠ 0` to
  find a point where δx_cv ≠ 0, then cancels to get ws/w = fx
- **Statement note**: The full "extract all 11 conditions from pixel equality" iff requires
  rational function coefficient extraction not supported by current helpers. PE-04b instead
  proves the CONDITIONAL iff: given all coefficient + projection conditions, pixel equality
  ↔ ws/w = fx. This is the key mathematical content of the paper's claim. See ambiguity
  register for the deliberate scope choice.
- **Proof strategy**: After all conditions substituted, pixel equality simplifies to
  `fx*δx + cx = (ws/w)*δx + cx` (radial parts cancel); specialize at (1,0) or (1,1)
  using `hp` to get δx ≠ 0; cancel to get ws/w = fx
- **Expected difficulty**: Medium.
- **Gate**: Compiles clean; extraction step for ws/w = fx is explicit
- **Dependencies**: SLICE-PE-03

### SLICE-PE-04c: Close the iff using PE-04b
- **Status**: NOT STARTED
- **Deliverable**: `opencv_openlensio_full_pipeline_pixel_iff` — remove sorry; wire in
  PE-04b helper for the → direction
- **Expected difficulty**: Low once PE-04b is done.
- **Gate**: Compiles clean; no sorry; proof review passes
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
