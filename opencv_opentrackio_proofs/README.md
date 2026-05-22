# opentrackio-proof

Formal Lean 4 proofs of the camera parameter conversion theorems from:

> "Conversion of OpenCV to OpenTrackIO (OpenLensIO) lens calibration parameters"  
> SMPTE RIS, corrected 2025-09-02

All theorems are proved using only Mathlib tactics (`field_simp`, `ring`, `linarith`, `nlinarith`, `norm_num`). No custom tactics or axioms beyond Lean's kernel.

## What is proved

The paper converts lens calibration parameters between two coordinate systems:

- **OpenCV** — upper-left-origin pixel coordinates; normalised distorted coordinates `(x', y')` with radius `r`
- **OpenTrackIO** — center-origin screen coordinates; screen-space radius `r_u = F·r`

### `PrincipalPointConversion.lean` — 5 theorems

The principal-point conversion `cx → ΔPx` is characterized completely.

| Theorem | Statement |
|---|---|
| `principal_point_conversion_necessary` | Consistency for all `x''` uniquely forces `F` and `ΔPx` to the corrected formulas |
| `principal_point_conversion_iff` | 1D consistency ↔ corrected `F` and `ΔPx` (necessary and sufficient) |
| `principal_point_conversion_2d_iff` | Full 2D consistency ↔ corrected `F`, `ΔPx`, `ΔPy` with a single scalar `F` |
| `single_focal_length_compatibility` | 2D consistency forces `(w/wₛ)·fx = (h/hₛ)·fy` — the condition under which OpenCV's separate `fx, fy` are exactly representable by one `F` |
| `buggy_principal_point_conversion_inconsistent` | The earlier erroneous formula `ΔPx = (w/wₛ)·cx` (missing the `-wₛ/2` centering term) is mathematically inconsistent with nonzero image dimensions |

The key insight: OpenCV uses upper-left-origin coordinates; OpenTrackIO uses center-origin. The `wₛ/2` term is not a correction to be applied — it is the *unique* value forced by requiring the two coordinate systems to agree on every scene point.

### `DistortionConversion.lean` — 8 theorems

The distortion parameter conversions `kᵢ → lᵢ` and `pᵢ → qᵢ` are characterized completely.

| Theorem | Statement |
|---|---|
| `radial_distortion_conversion` | `∀r, k·r^(2n) = l·(F·r)^(2n)` → `l = k/F^(2n)` (per-term, any degree) |
| `tangential_q1_conversion` | `∀x'y', p1·x'·y' = q1·(Fx')·(Fy')` → `q1 = p1/F²` |
| `tangential_q2_conversion` | `∀rx', p2·(r²+2x'²) = q2·(…)` → `q2 = p2/F²` |
| `whole_radial_polynomial_iff` | Full numerator polynomial equal for all `r` ↔ `l1=k1/F²`, `l3=k2/F⁴`, `l5=k3/F⁶` |
| `whole_tangential_field_iff` | Full tangential `δx` equal for all `(x',y')` ↔ `q1=p1/F²`, `q2=p2/F²` |
| `whole_tangential_field_2d_iff` | Full tangential vector field `(δx, δy)` equal for all `(x',y')` ↔ same conversions |
| `all_distortion_conversions_iff` | Both radial polynomials and the 2D tangential field equal ↔ all 8 parameter conversions |
| `radial_coefficients_imply_rational_factor_equality` | Coefficient conversions → rational radial scale factors agree pointwise |

The `whole_*_iff` theorems are the strongest form: they prove the conversions are *necessary*, not merely sufficient. The `→` directions derive coefficient uniqueness by specializing the polynomial identity at enough points and solving the resulting linear system via `nlinarith`.

### `PixelEquivalence.lean` — 2 theorems

End-to-end pixel coordinate preservation, connecting the two preceding files.

| Theorem | Statement |
|---|---|
| `linear_projection_pixel_equivalence_2d_iff` | The linear (pinhole) projection agrees in both models for all `(x, y)` ↔ the principal-point conversion formulas hold. Direct restatement of `principal_point_conversion_2d_iff` in pipeline form. |
| `radial_distortion_value_equivalence` | The rational radial scale factor has the same value in both models at corresponding radii (`r` in OpenCV, `r_u = F·r` in OpenTrackIO), given the coefficient conversions. Also derives that the OpenTrackIO denominator is nonzero whenever the OpenCV denominator is. |

Full end-to-end pipeline equivalence is proved in `Pipeline/` — see below.

### `Pipeline/` — 3 theorems

Full pipeline equivalence: both radial and tangential distortion composed with linear projection.

| Theorem | Statement |
|---|---|
| `opencv_openlensio_radial_pipeline_eq` | The radial-only pipelines agree at corresponding points after parameter conversion. Follows from `radial_distortion_value_equivalence`. |
| `opencv_openlensio_full_pipeline_pixel_sufficiency` | Given all parameter conversions *and* `wₛ/w = fx`, the full pixel x-outputs agree for every normalised input. |
| `opencv_openlensio_full_pipeline_pixel_iff` | Given all parameter conversions and at least one nonzero tangential coefficient, the full pixel x-outputs agree for every normalised input **if and only if** `wₛ/w = fx`. |

The key result is the iff. The radial components agree automatically after conversion. The tangential components differ by the scalar factor `(wₛ/w − fx)` applied to the OpenCV tangential term: after substituting all conversions, universal pixel agreement reduces to `(fx − wₛ/w) · T(x',y') = 0` for all `(x', y')`, where `T` is the CV tangential polynomial. Since `T` is not identically zero when `p1 ≠ 0 ∨ p2 ≠ 0`, the factor must vanish, giving `wₛ/w = fx`.

The theorem is an x-component proof (the y-component is symmetric). The forward direction requires `p1 ≠ 0 ∨ p2 ≠ 0`; a pure-radial lens does not constrain `wₛ/w`.

## Future work

Natural extensions not yet proved:

- **y-coordinate symmetry** — the y-component proof is symmetric to the x-component (p1 ↔ p2 swapped); not yet written.
- **Full 2D point equivalence** — a single theorem combining x and y, showing both components agree iff `wₛ/w = fx`.
- **Pure-radial special case** — when `p1 = p2 = 0`, `wₛ/w = fx` is not entailed by pixel agreement; a separate theorem characterizing the pure-radial case is not yet proved.

## Building

Requires [elan](https://github.com/leanprover/elan) (the Lean version manager). The toolchain and Mathlib version are pinned in `lean-toolchain` and `lakefile.toml`.

```sh
lake update   # downloads Mathlib (one-time, ~1GB cache)
lake build
```

Expected output: `Build completed successfully (N jobs).`

The build takes several minutes on first run due to Mathlib compilation. Subsequent builds are cached.

## Repository layout

```
lakefile.toml                       Lake build configuration
lean-toolchain                      Lean 4 version pin (v4.29.0)
opencv_opentrackio_proofs/
  PrincipalPointConversion.lean
  DistortionConversion.lean
  PixelEquivalence.lean
  PipelineEquivalence.lean          Re-export shim for Pipeline/
  Pipeline/
    OpenCVModel.lean                undistortXCV, undistortYCV definitions
    RadialPipeline.lean             opencv_openlensio_radial_pipeline_eq
    PixelSufficiency.lean           opencv_openlensio_full_pipeline_pixel_sufficiency
    PixelIffHelpers.lean            Helper lemmas (namespace PipelineEquivalence)
    PixelIff.lean                   opencv_openlensio_full_pipeline_pixel_iff
    README.md                       Pipeline/ proof summary
```

## Source

The paper is available from SMPTE RIS:  
https://ris-pub.smpte.org/ris-osvp-metadata-camdkit/res/OpenCV_to_OpenTrackIO.pdf
