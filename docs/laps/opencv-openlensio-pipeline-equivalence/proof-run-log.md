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

## SLICE-PE-04b: pixel_eq_implies_tangential_gap

### Attempt 1 (2026-05-22)

**Strategy**: 
- Add `pixel_eq_implies_tangential_gap` to `PixelIffHelpers.lean`.
- `intro x' y'`, instantiate h_rad, h_tang, h_offset, h_scale.
- `rw [h_rad, h_tang] at hspec`.
- `linear_combination hspec + R_x * h_scale + h_offset`.

**Outcome**: `rw [h_rad]` succeeded. `rw [h_tang]` failed.

**Error**: `Tactic rewrite failed: Did not find an occurrence of the pattern`
```
2 * q1 * (F * x') * (F * y') + q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2)
```

**Root cause (classified)**: Associativity mismatch. The OTI tangential term is a sum of two terms `A + B` inside a left-associative four-term sum `((R_x*F + A) + B) + ΔPx`. The sum `A + B` is not a contiguous subterm at any associativity level — `A` is the right child of `R_x*F + A`, and `B` is the right child of `(R_x*F+A) + B`. The pattern `A + B` is not reachable by syntactic `rw`.

**Next move**: Split h_tang into two separate lemmas `h_tang1 : A = A'` and `h_tang2 : B = B'`, and do `rw [h_rad, h_tang1, h_tang2]`. Individual subterms A and B ARE accessible.

### Attempt 2 (2026-05-22)

**Strategy**: Replace `h_tang` with `h_tang1 : 2*q1*(F*x')*(F*y') = 2*p1*x'*y'` and `h_tang2 : q2*((F*x')^2+(F*y')^2+2*(F*x')^2) = p2*(x'^2+y'^2+2*x'^2)`. After `rw [h_rad, h_tang1, h_tang2]`, all OTI tangential atoms match CV tangential atoms, and `linear_combination` closes via ring.

**Outcome**: Clean compile. Both `h_tang1` and `h_tang2` are proved by `rw [hq_i]; field_simp [hF2]` (field_simp closes each goal without `ring`). `rw [h_rad, h_tang1, h_tang2] at hspec` succeeds — each individual tangential term is a contiguous subterm at its associativity level. `linear_combination` closes the goal. `PixelIff.lean` → direction filled; `lake build PipelineEquivalence` completes with no errors (2026-05-22).

## SLICE-PE-04c: Remove sorry — forward direction composition

### Attempt 1 (2026-05-22)

**Strategy**: Replace `intro _h; sorry` in `PixelIff.lean` with `intro h; exact tangential_gap_forces_scale ... (pixel_eq_implies_tangential_gap ... h)`.

**Outcome**: Clean compile. `lake build PipelineEquivalence` — 3298 jobs, all succeed (2026-05-22). No sorry remains in the Pipeline/ files.
