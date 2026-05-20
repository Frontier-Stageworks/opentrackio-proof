---
name: openlensio-semantics-first-slice-contract
description: First-slice contract for openlensio_semantics; defines the minimum deliverable for the initial implementation slice
metadata:
  type: reference
---

# First-Slice Contract — `openlensio_semantics`

**Task slug:** `openlensio-semantics`  
**Phase:** Pre-implementation (Gate 1–3 pending)  
**First implementation slice:** SLICE-OL-00 + SLICE-OL-01 + SLICE-OL-03

---

## Scope

The first implementation slice delivers:

1. **SLICE-OL-00**: A compiling `openlensio_semantics` Lean project with correct imports from `opentrackio_parser`, no theorems yet, just the skeleton.

2. **SLICE-OL-01**: The types `LensSemantics`, `RadialCoefficients`, `TangentialCoefficients`, `ProjectionParameters`, and `ValidLensSemantics`. No decoder, no theorems — type definitions only.

3. **SLICE-OL-03**: The theorem `semanticExtraction_sound` connecting the semantic bridge to `ValidLensSemantics`.

## NOT in scope for first slice

- The distortion function U(ϵ)
- Any projection model
- Coordinate-space types beyond `SensorPoint`
- Any equivalence theorems
- Executable oracle
- Overscan

## Entry conditions

Gates 0, 1, 2, 3 must pass before implementation begins:
- [x] Gate 0: Spec extraction complete (this document)
- [ ] Gate 1: Existing-proof boundary review
- [ ] Gate 2: Ambiguities triaged (AMB-OL-007 handling documented)
- [ ] Gate 3: Representation choices reviewed and approved

## Acceptance criteria for first slice

1. `lake build openlensio_semantics` succeeds without `sorry`
2. `ValidLensSemantics` includes at minimum:
   - `focalLength > 0`
   - `sensorWidth > 0`
   - An explicit denominator nonzero condition for the coefficient tuple
3. `semanticExtraction_sound` is proved without `sorry`
4. The statement of `semanticExtraction_sound` is reviewed: confirm that `ValidLensSemantics` is not vacuously satisfied by checking it against at least one invalid input
5. AMB-OL-007 documented in proof capsule: denominator nonzero is a hypothesis, not proved

## What happens after first slice

After the first slice is reviewed and committed:
- Open Gate 4 (domain-safety review)
- Proceed to SLICE-OL-04 (coordinate-space types)
- Update work-queue.md with completed slices
