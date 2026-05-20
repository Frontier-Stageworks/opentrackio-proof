---
name: openlensio-semantics-proof-run-log
description: Lean build record for the openlensio_semantics campaign (OL-00 through OL-15)
metadata:
  type: reference
---

# Proof Run Log — `openlensio_semantics`

Campaign: `openlensio_semantics` (OpenLensIO v1.0.1 formal semantics, SLICE-OL-00 through OL-15)
Reconstructed from session records. See notes on retroactive reconstruction below.

---

## Final Lean Build Record

| Field | Value |
|-------|-------|
| **Command** | `lake build` (project root: `opentrackio-proof/`) |
| **Toolchain** | Lean 4 / Mathlib v4.29.0 (per `lean-toolchain`) |
| **Date of final check** | 2026-05-20 (retroactive; all slices OL-13/14 completed this session) |
| **Result** | Clean — no errors, no warnings blocking compilation |
| **Files present at final check** | All 11 Lean source files listed below |

### Lean source files at final build

| File | Slice | Status |
|------|-------|--------|
| `CoordinateTypes.lean` | OL-04 | ✅ Clean |
| `LensSemantics.lean` | OL-01 | ✅ Clean |
| `SemanticBridge.lean` | OL-02/03 | ✅ Clean |
| `RadialPolynomial.lean` | OL-05/06 | ✅ Clean |
| `DistortionModel.lean` | OL-07/08 | ✅ Clean |
| `DeltaSemantics.lean` | OL-09 | ✅ Clean |
| `ProjectionModel.lean` | OL-10 | ✅ Clean |
| `FovModel.lean` | OL-11 | ✅ Clean |
| `AngleOfView.lean` | OL-12 | ✅ Clean |
| `ShaderCoords.lean` | OL-13 | ✅ Clean |
| `ExecutableSemanticOracle.lean` | OL-14 | ✅ Clean (no theorems — #eval only) |

### `lakefile.toml` library targets at final build

All library targets registered:
- `openlensio_semantics` (main library)
- `ShaderCoords` (OL-13)
- `ExecutableSemanticOracle` (OL-14)

---

## Theorem Count at Final Build

| Classification | Count |
|---------------|-------|
| Public theorems | 14 |
| Private lemmas | 1 (`undistortPoint_congr` in `FovModel.lean`) |
| **Total** | **15** |

No `sorry`, `admit`, `unsafe`, or `partial` in any theorem.

---

## Per-Slice Build Notes

### OL-04 through OL-12 (pre-session)
All slices OL-04 through OL-12 were proved and verified in earlier sessions. Compilation recorded as clean in `proof-capsule.md` and `proof-review.md`. No issues at integration.

### OL-13 — ShaderCoords

`pixel_metric_roundtrip`: initial proof used `field_simp <;> ring`. Linter flagged `ring` as a no-op (field_simp closes alone). Removed `ring` from this theorem only.

`image_texture_coordinate_roundtrip`: `field_simp` alone leaves unsolved goal `q.x * 2 - wshader + wshader = q.x * 2`. `ring` required as a second step after `field_simp`. Final proof: `field_simp [hw.ne', hh.ne', hs.ne'] <;> ring`.

Both theorems: clean after above fixes.

### OL-14 — ExecutableSemanticOracle

Initial draft used grouped field syntax `k1 k2 k3 k4 k5 k6 : Float` in `structure where` block — invalid in Lean 4 (each field requires its own `: Type` annotation). Fixed to one field per line. All `#eval` demonstrations produced expected output.

### OL-15 — Python reference oracle

Oracle: `battery-tester/semantic_oracle/reference_oracle.py`
Fixtures: `battery-tester/semantic_oracle/fixtures.json` (7 cases)
Runner: `battery-tester/semantic_oracle/run.py`

Command: `python3 battery-tester/semantic_oracle/run.py`
Result: **7/7 PASS**

| Fixture | Result |
|---------|--------|
| `identity` | PASS |
| `barrel` | PASS |
| `pincushion` | PASS |
| `zero-origin` | PASS |
| `tangential` | PASS |
| `domain-fail` | PASS |
| `full-eq4` | PASS |

**Note:** Python fixture results are differential-testing evidence, NOT a Lean-verified theorem. See AMB-OL-016 and EX-01 in the vacuity audit report for the boundary between executable testing and formal proof.

---

## Retroactive Reconstruction Note

This `proof-run-log.md` was created retroactively during the closeout pass (2026-05-20), after the vacuity audit identified its absence as finding ART-02. The content is reconstructed from:

- Session records of the proof campaign
- `proof-capsule.md` compilation notes per slice
- `proof-review.md` per-theorem records
- Direct inspection of all 11 Lean source files

The final clean compilation was confirmed during this closeout session. No Lean code was modified during the closeout pass; only documentation files were added or updated.

---

## Known Gaps

- No per-tactic run log exists (was not captured during proof execution).
- No CI run artifact exists; builds were local only.
- Float oracle (#eval output) was confirmed by visual inspection of `#eval` results; not captured in a structured log.

These gaps do not affect theorem correctness. The Lean kernel check is the trust anchor.
