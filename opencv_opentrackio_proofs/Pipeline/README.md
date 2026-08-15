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

## Future work

Natural extensions and open gaps:

- **y-coordinate symmetry** — the y-component proof is symmetric to the x-component (p1 ↔ p2 swapped); not yet written.
- **Full 2D point equivalence** — a single theorem combining x and y, showing both pixel coordinates agree iff `wₛ/w = fx`.
- **Pure-radial special case** — when `p1 = p2 = 0`, `wₛ/w = fx` is not entailed by pixel agreement. The iff theorem does not cover this case; a separate characterization of when purely-radial pipelines agree is not yet proved.
- **Semantic validity packaging** — `wₛ/w = fx` together with the coefficient conversions could be packaged as a `ValidPipelineAlignment` predicate that mirrors the existing `ValidLensSemantics` structure, making the equivalence condition a first-class type-level invariant.
- **Connection to parsed OpenTrackIO/OpenLensIO fields** — the hypotheses here (`hF_eq`, `hΔPx`, `hl1`…`hq2`) are stated as abstract real-number conditions; linking them to the decoded `LensModel` and `CameraModel` fields from the parser library would close the gap between the formal proof and a live OpenTrackIO sample.
- **Domain validation layer** — the proofs assume `hden` (denominator nonzero everywhere), `hF : F ≠ 0`, `hw : w ≠ 0`, `hws : ws ≠ 0` as free hypotheses. A validation layer that derives these from physically-meaningful bounds (positive sensor dimensions, positive focal length, denominator bounded away from zero over a working range) would make the theorems applicable to concrete calibration data.

## Dependencies

- Lean 4 v4.29.0, Mathlib v4.29.0
- `DistortionConversion` (same library) — parameter conversion formulas
- `DistortionModel` (`openlensio_semantics`) — OTI pipeline definitions and `radialTerm`
- `PixelEquivalence` (same library) — `radial_distortion_value_equivalence`

## Investigation: suspected paper-level tangential conversion bug

**`PixelIffCorrected.lean`** is a separate investigation, not part of the
as-published formalization above. It does not modify `PixelIff.lean`,
`PixelIffHelpers.lean`, `PixelSufficiency.lean`, or `RadialPipeline.lean` —
all of those remain an exact, unmodified formalization of what the source
paper states, including its stated `q1 = p1/F², q2 = p2/F²` tangential
conversion.

The investigation's hypothesis: the paper's own coordinate map for the
*distorted* point, `ε'_x,d = F·x''`, implies the tangential displacement
should convert as `δx_oti = F·δx_cv` (one factor of F, since the displacement
is additive) rather than `δx_oti = δx_cv` (the paper's literal stated
equation, zero factors of F). Re-deriving `q1, q2` under the corrected
condition gives `q1 = p1/F, q2 = p2/F` — one power of F, not two. The radial
conversion is unaffected (it is multiplicative, so its F is already carried
through the coordinate's own scaling).

`opencv_openlensio_full_pipeline_pixel_corrected` proves that under this
corrected conversion, full pixel-x agreement holds **unconditionally** — the
`ws/w = fx` condition required by `opencv_openlensio_full_pipeline_pixel_iff`
does not survive. `physical_pixel_agreement_scale_independent_example` gives
a concrete numeric witness with `ws/w ≠ fx` where pixel agreement still
holds, mechanically confirming that the naive ported iff
(`pixel_eq ↔ ws/w = fx`) is false under the corrected hypotheses, not merely
unproved.

This is presented as an open question about the source paper, not as a
correction to this repository's formalization of it. See
`docs/laps/tangential-conversion-physical-fix/` for the full derivation and
review, and `DistortionConversionCorrected.lean` (top-level, sibling of
`DistortionConversion.lean`) for the corresponding corrected parameter-level
theorems.
