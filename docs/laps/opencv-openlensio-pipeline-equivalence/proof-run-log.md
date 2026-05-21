---
name: opencv-openlensio-pipeline-equivalence-proof-run-log
description: Run-by-run proof attempt log for SLICE-PE-02 through PE-04
metadata:
  type: project
---

# Proof Run Log — OpenCV/OpenLensIO Pipeline Equivalence

## SLICE-PE-02: opencv_openlensio_radial_pipeline_eq

### Attempt 1

**Strategy**: Use `tangential_zero_coefficients_identity` to reduce OTI side to `radialTerm * coord`; unfold `undistortXCV` with zero tangential; unfold `radialTerm`; apply `h_rscale`; apply `radial_distortion_value_equivalence`; close by `ring`.

**Outcome**: First attempt had two errors: (1) missing `import PixelEquivalence` for `radial_distortion_value_equivalence`; (2) struct literal projections `⟨l1,...⟩.k1` not reduced by `simp only [radialTerm]` alone. Fixed: added import; replaced inline `simp only [radialTerm, h_rscale]` with a named `have h_rterm` relying on `simp only [radialTerm, h_rscale]` (struct projections then reduce by `rfl` inside that have). Final proof compiles clean.

**Lean check**: `lake env lean opencv_opentrackio_proofs/PipelineEquivalence.lean` — no output (2026-05-21).

## SLICE-PE-03: opencv_openlensio_full_pipeline_pixel_sufficiency

### Attempt 1

**Strategy**: Introduce `x' y'`; use `have` blocks to establish OTI denominator nonzero (`h_den_oti`), radial num/den equalities; substitute via `rw [hq1, hq2, hΔPx, hscale, hF_eq]`; close with `field_simp [hw, hws]; ring`.

**Outcome**: Two errors.

**Error 1** (line 210): `linarith failed` in `h_den_oti`. After `field_simp [hF2, hF4, hF6]`, the hypothesis goal had `k5 * (x'^2+y'^2)^2` reordered to `(x'^2+y'^2)^2 * k5`; `linarith` treats these as distinct terms and cannot close.

**Error 2** (line 235): `ring` fails after `field_simp [hw, hws]`. Root cause: `rw [hscale]` put `fx` in the goal (replacing `ws/w`), but `field_simp [hw, hws]` then introduced `fx⁻¹` because it doesn't know `fx ≠ 0`. The resulting goal had hundreds of `fx⁻¹` terms that `ring` cannot close.

### Attempt 2

**Strategy**: 
- Remove `h_den_oti` entirely — after `rw [h_den]` rewrites the OTI denominator to the CV expression, `hden_xy` serves as the nonzero witness; `h_den_oti` is unused.
- Derive `hws_eq : ws = w * fx` from `hscale` (clearing denominator via `div_eq_iff` + `mul_comm`).
- Derive `hfx : fx ≠ 0` from `hscale` + `hws` + `hw`.
- Replace closing `rw [hscale, hF_eq]; field_simp [hw, hws]; ring` with `rw [hF_eq, hws_eq]; field_simp [hw, hfx, hden_xy]; ring`. This eliminates `ws` via `hws_eq` (so `w/(w*fx)*fx = 1`) and clears fractions with nonzero witnesses `hw`, `hfx`, `hden_xy`.

**Lean check**: `lake env lean opencv_opentrackio_proofs/PipelineEquivalence.lean` — no errors (one unused-variable warning for `hF_pos`) (2026-05-21).
