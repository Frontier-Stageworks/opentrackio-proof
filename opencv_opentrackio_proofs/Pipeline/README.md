# OpenCV / OpenLensIO Pipeline Equivalence

This directory contains a machine-checked proof of the conditions under which the
OpenCV Brown-Conrady undistortion pipeline and the OpenLensIO (OTI) undistortion
pipeline produce identical pixel output.

## Background

Both pipelines implement the same distortion model but differ in coordinate convention.
OpenCV evaluates the radial and tangential terms at the *normalised* radius r, then
applies a linear projection to reach pixel coordinates. OTI evaluates the same terms
at the *screen-space* radius F·r, where F = (w/ws)·fx is derived from sensor geometry
and focal length. Prior work (in `DistortionConversion.lean` and `PixelEquivalence.lean`)
formalised the *parameter conversion formulas* — the algebraic relationships between
the coefficient sets (k→l, p→q, cx→ΔPx) that make the two denominations correspond.
That work does not address what each pipeline *computes* at an image point.

This work closes that gap.

## Main Result

**Theorem** (`opencv_openlensio_full_pipeline_pixel_iff`): Given all parameter
conversions hold — radial numerator/denominator coefficients rescaled by powers of
F, tangential coefficients rescaled by F², projection offset ΔPx derived from cx —
and given at least one tangential coefficient is nonzero, the x-pixel outputs of the
two pipelines agree for every normalised input point if and only if

    ws / w = fx

where ws is the OTI sensor width in pixels, w is the physical sensor width, and fx
is the OpenCV focal length in pixels.

The condition ws/w = fx is the exact additional requirement beyond parameter conversion.
The radial components automatically agree after conversion; the tangential components
differ by the scalar factor (ws/w − fx) applied to the CV tangential term. When this
scalar is nonzero and the tangential polynomial is not identically zero, the pipelines
diverge at every point where the tangential contribution is nonzero.

## Key Mathematical Insight

After substituting all conversion hypotheses into the pixel equality, the equation
reduces to

    (fx − ws/w) · (2·p1·x'·y' + p2·(x'² + y'² + 2·x'²)) = 0   for all x', y'

The radial rational functions cancel exactly. The tangential polynomial is not
identically zero when p1 ≠ 0 or p2 ≠ 0, so the scalar factor must be zero, giving
ws/w = fx.

## Scope

- **Component**: x-coordinate only. The y-component is symmetric (p1 ↔ p2 swapped)
  and is deferred.
- **Iff shape**: The theorem is a *conditional* iff — all parameter conversion
  hypotheses are given as context, and the iff isolates ws/w = fx as the remaining
  condition. The full unconditional extraction of all eleven conditions from pixel
  equality alone is not proved here.
- **Tangential hypothesis**: The forward direction requires p1 ≠ 0 ∨ p2 ≠ 0. For a
  pure-radial lens (p1 = p2 = 0), ws/w = fx is not entailed by pixel equality and
  the theorem does not apply.
- **Denominator regularity**: The proof assumes the rational radial denominator is
  nonzero at every input point; this is supplied as a universal hypothesis `hden`.

## Files

| File | Contents |
|------|----------|
| `OpenCVModel.lean` | Definitions of `undistortXCV`, `undistortYCV`, `undistortPointCV` |
| `RadialPipeline.lean` | `opencv_openlensio_radial_pipeline_eq` — radial-only agreement |
| `PixelSufficiency.lean` | `opencv_openlensio_full_pipeline_pixel_sufficiency` — ← direction standalone |
| `PixelIffHelpers.lean` | Five helper lemmas in `namespace PipelineEquivalence` |
| `PixelIff.lean` | `opencv_openlensio_full_pipeline_pixel_iff` — the main iff theorem |

## Dependencies

- Lean 4 v4.29.0, Mathlib v4.29.0
- `DistortionConversion` (same library) — parameter conversion formulas
- `DistortionModel` (`openlensio_semantics`) — OTI pipeline definitions and `radialTerm`
- `PixelEquivalence` (same library) — `radial_distortion_value_equivalence`
