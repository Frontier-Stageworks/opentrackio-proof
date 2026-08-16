# OpenCV Cross-Check — Real-Lens Sanity Check

## What this is

A scaffolding **sanity check on this repository's own OpenCV-formula
transcription** — it checks that the Python port of the OpenCV
forward-distortion formula and the two tangential-conversion formulas
(`DistortionConversion.lean`'s paper-published `q1=p1/F², q2=p2/F²`, and
`DistortionConversionCorrected.lean`'s corrected `q1=p1/F, q2=p2/F`) match
what is already proven in Lean, illustrated with **one real, published
camera calibration** instead of a synthetic `F=50` toy example.

## What this is NOT

**Not independent evidence for the F-vs-F² question.** That question is
already settled exactly, for every input in its domain, by the Lean proofs
in `DistortionConversionCorrected.lean` and
`Pipeline/PixelIffCorrected.lean` (see
`docs/laps/tangential-conversion-physical-fix/`). Running eight numeric
points through a hand-written Python port cannot add confidence beyond what
the kernel-checked proof already provides — at best it can only *fail to
catch* a transcription bug, never *prove* the underlying math. Its value is
narrower: confirming this repo's Python transcription of the formulas is
correct, and giving readers a concrete, non-synthetic illustration of what
the theorems mean in practice.

**Not a differential test against an authoritative external
implementation.** Both sides of every comparison here are written by this
repository (a hand-rolled OpenCV forward-distortion function, and
`battery-tester/semantic_oracle/reference_oracle.py`'s OpenTrackIO oracle,
reused unmodified). A genuine differential test would need a *third*, truly
independent implementation — e.g., checking whether
[`opentrackio-cpp`](https://github.com/SMPTE/opentrackio-cpp)'s actual
lens-distortion-*consuming* code (if any exists beyond `dump_sample`)
treats `q1`/`q2` the way this formalization assumes. That is flagged as
follow-up work below, not attempted here.

**Not using real `cv2`.** OpenCV's own `cv2.undistortPoints` solves the
*inverse* problem (removing distortion from a captured image) via numerical
iteration — a different computation from the closed-form *forward*
Brown-Conrady formula (`x'' = x'·R(r) + tangential(x',y')`) that
`Pipeline/OpenCVModel.lean` formalizes and that the SMPTE RIS paper's
conversion theorems are about. Calling real `cv2` here would compare our
proofs against an unrelated numerical method and introduce iterative-solver
noise that has nothing to do with the F-vs-F² question.

## Structure

Follows `battery-tester/semantic_oracle/`'s layout:

| File | Contents |
|---|---|
| `reference_impl.py` | OpenCV forward-distortion formula (ported from `Pipeline/OpenCVModel.lean`) + parameter conversion (ported from `DistortionConversion.lean` / `DistortionConversionCorrected.lean` / `PrincipalPointConversion.lean`), both modes |
| `fixtures.json` | One real camera calibration + a grid of normalised test points |
| `run.py` | Runner: OpenCV ground truth vs. both OpenTrackIO conversions, per point |

## The fixture

A real OpenCV-format calibration — not synthetic numbers — computed by the
Camera Calibration Toolbox for MATLAB (Bouguet/Caltech) from three real
photographs of a checkerboard, taken 2012-05-24. The source images were
downloaded and inspected directly: EXIF metadata confirms
`model=FinePix6900ZOOM` (a real Fujifilm digital camera) at its native
`2048×1536` resolution. Physical sensor size (7.60mm × 5.70mm) is the
standard published dimension for that camera's documented 1/1.7" CCD format
— OpenCV calibration alone only determines focal length in pixel units, not
physical sensor size, so this one field is a labeled, standard-format
assumption rather than something read off the calibration itself; everything
else in the fixture (`fx, fy, cx, cy, k1, k2, k3, p1, p2`, pixel resolution)
comes directly from the cited real calibration. See `fixtures.json` for the
full source citation and per-field notes.

Test points are a small grid of normalised `(x', y')` coordinates: two near
center, two mid-radius, four near the image edge (where the tangential term
is largest) — chosen to exercise the tangential distortion meaningfully
rather than vanish at `r≈0`.

## Running

```sh
cd battery-tester/opencv_cross_check
python3 run.py
```

Expected outcome (and what actually happens): the **corrected** conversion's
x-output matches the OpenCV ground truth to machine epsilon at every point —
this is the algebraic identity
`opencv_openlensio_full_pipeline_pixel_corrected` proves, so an exact match
here is not a coincidence, it is that theorem holding at these eight
concrete points. The **paper** conversion's x-output visibly diverges (from
~0.02px near center up to ~7.5px at the edge points) — expected, since this
real fixture's `ws/w` is nowhere near `fx`, and
`opencv_openlensio_full_pipeline_pixel_iff` proves paper-conversion pixel
agreement requires exactly `ws/w = fx`. **A "FAIL" on the paper conversion's
x-column is the correct, expected result, not a bug in this script.**

The y-columns are printed for information only and are excluded from the
pass/fail verdict: this fixture's real calibration has `fx ≠ fy`, so the
single-scalar-`F` OpenTrackIO model cannot exactly reproduce OpenCV's
y-pixel output under *either* conversion, regardless of the tangential
formula — a separate, already-documented limitation
(`single_focal_length_compatibility` in `PrincipalPointConversion.lean`; see
also `fixtures.json`'s `aspect_ratio_note`). Folding that unrelated residual
into the x pass/fail would obscure the one thing this script is meant to
show. This also matches the scope of the formally proven pipeline theorems
themselves — `opencv_openlensio_full_pipeline_pixel_iff` / `_sufficiency` /
`_corrected` are all x-only (see `docs/limitations.md`).

## Follow-up work (not attempted here)

A genuine differential test needs a third, independent implementation. The
most promising candidate in this ecosystem: check whether
[`opentrackio-cpp`](https://github.com/SMPTE/opentrackio-cpp) has any
lens-distortion-*consuming* code beyond sample dumping/parsing (its current
scope appears to be a decoder like this repo's `opentrackio_parser/`, not a
distortion-applying renderer) — and if such code exists now or is added
later, check whether it treats `q1`/`q2` as `p1/F², p2/F²` or `p1/F, p2/F`.
That would be genuine external evidence either way. Not attempted in this
task.
