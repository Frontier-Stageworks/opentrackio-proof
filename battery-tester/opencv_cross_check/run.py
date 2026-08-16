#!/usr/bin/env python3
"""
battery-tester/opencv_cross_check/run.py

Scaffolding sanity check on this repository's own OpenCV-formula
transcription, illustrated with one real-lens calibration. See README.md —
this is NOT a differential test against an authoritative external
implementation, and it does NOT adjudicate the F-vs-F^2 tangential-conversion
question. The Lean proofs already settle that exactly, for all inputs; this
script exercises a handful of concrete points from one real camera as a
readable, non-synthetic illustration, and as a check that the Python port of
the paper/corrected formulas matches the already-proven Lean formulas.

For each normalised test point (x', y'):
  - ground truth: OpenCV forward Brown-Conrady pixel output (reference_impl's
    port of Pipeline/OpenCVModel.lean's undistortXCV/undistortYCV)
  - OpenTrackIO pixel output under the "paper" tangential conversion
    (q_i = p_i/F^2, DistortionConversion.lean)
  - OpenTrackIO pixel output under the "corrected" tangential conversion
    (q_i = p_i/F, DistortionConversionCorrected.lean)

Pass/fail is reported for the x-coordinate only, matching the scope of the
formally proven pipeline theorems (opencv_openlensio_full_pipeline_pixel_iff /
_sufficiency / _corrected are all x-only; see docs/limitations.md). The
y-coordinate is printed for information but is not part of the pass/fail
verdict: this fixture's real calibration has fx != fy, so the single-scalar-F
OpenTrackIO model cannot exactly reproduce OpenCV's y-pixel output regardless
of the tangential conversion used (see fixtures.json's aspect_ratio_note and
single_focal_length_compatibility in PrincipalPointConversion.lean) — folding
that unrelated, expected residual into the x pass/fail would obscure the one
thing this script is meant to show.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from reference_impl import (
    opencv_pixel,
    convert_params,
    oti_pixel_x,
    oti_pixel_y,
)

FIXTURES_PATH = Path(__file__).parent / "fixtures.json"

# Tolerance for the x-coordinate pass/fail. Not a numerical-noise margin in
# the usual floating-point sense — the "corrected" conversion is algebraically
# exact per opencv_openlensio_full_pipeline_pixel_corrected, so its residual
# is expected to be at machine epsilon. The "paper" conversion's residual is
# expected to be large (pixels, not epsilon) whenever the tangential term is
# non-negligible, per opencv_openlensio_full_pipeline_pixel_iff's ws/w = fx
# requirement — this fixture's real ws/w and fx are nowhere near equal, so
# "paper" is EXPECTED to fail. A failing "paper" row is the correct, expected
# outcome, not a bug in this script.
X_TOLERANCE_PX = 1e-6


def main() -> None:
    fixtures = json.loads(FIXTURES_PATH.read_text())
    cal = fixtures["calibration"]

    fx, fy = cal["fx"], cal["fy"]
    cx, cy = cal["cx"], cal["cy"]
    k_cv = [cal["k1"], cal["k2"], cal["k3"], 0.0, 0.0, 0.0]
    p_cv = [cal["p1"], cal["p2"]]
    ws = float(cal["pixel_resolution"]["width"])
    hs = float(cal["pixel_resolution"]["height"])
    w = float(cal["sensor_physical_mm"]["width"])
    h = float(cal["sensor_physical_mm"]["height"])

    print(f"Calibration: {cal['id']}")
    print(f"  fx={fx}, fy={fy}, cx={cx}, cy={cy}")
    print(f"  k1={k_cv[0]}, k2={k_cv[1]}, k3={k_cv[2]}, p1={p_cv[0]}, p2={p_cv[1]}")
    print(f"  pixel resolution: {ws:.0f}x{hs:.0f}, sensor: {w}mm x {h}mm")
    print()

    F_paper, dpx_paper, dpy_paper, l_paper, q_paper = convert_params(
        fx, fy, cx, cy, w, ws, h, hs, k_cv, p_cv, "paper"
    )
    F_corr, dpx_corr, dpy_corr, l_corr, q_corr = convert_params(
        fx, fy, cx, cy, w, ws, h, hs, k_cv, p_cv, "corrected"
    )
    # F, dpx, dpy, l1-l6 do not depend on mode; only q1, q2 differ.
    assert F_paper == F_corr and dpx_paper == dpx_corr and l_paper == l_corr
    print(f"F={F_paper:.6f}  dpx={dpx_paper:.6f}  dpy={dpy_paper:.6f}")
    print(f"  q (paper)     = {q_paper}")
    print(f"  q (corrected) = {q_corr}")
    print()

    header = (
        f"{'point':<16}{'cv_x':>12}{'cv_y':>12}"
        f"{'paper_x':>12}{'paper_dx':>12}{'STATUS':>8}"
        f"{'corr_x':>12}{'corr_dx':>12}{'STATUS':>8}"
        f"{'paper_y*':>12}{'corr_y*':>12}"
    )
    print(header)
    print("-" * len(header))

    passed = 0
    failed = 0
    for pt in fixtures["test_points"]:
        xp, yp = pt["x"], pt["y"]
        cvx, cvy = opencv_pixel(fx, fy, cx, cy, k_cv, p_cv, xp, yp)

        px_paper = oti_pixel_x(ws, w, F_paper, dpx_paper, l_paper, q_paper, xp, yp)
        px_corr = oti_pixel_x(ws, w, F_corr, dpx_corr, l_corr, q_corr, xp, yp)
        py_paper = oti_pixel_y(hs, h, F_paper, dpy_paper, l_paper, q_paper, xp, yp)
        py_corr = oti_pixel_y(hs, h, F_corr, dpy_corr, l_corr, q_corr, xp, yp)

        if px_paper is None or px_corr is None:
            print(f"{pt['id']:<16} DOMAIN FAILURE (radial denominator near zero)")
            failed += 1
            continue

        dx_paper = abs(px_paper - cvx)
        dx_corr = abs(px_corr - cvx)
        status_paper = "PASS" if dx_paper <= X_TOLERANCE_PX else "FAIL"
        status_corr = "PASS" if dx_corr <= X_TOLERANCE_PX else "FAIL"

        # Only the corrected conversion's x-result is expected to pass; the
        # script's own success/failure exit code tracks that expectation.
        if status_corr == "PASS":
            passed += 1
        else:
            failed += 1

        print(
            f"{pt['id']:<16}{cvx:12.4f}{cvy:12.4f}"
            f"{px_paper:12.4f}{dx_paper:12.6f}{status_paper:>8}"
            f"{px_corr:12.4f}{dx_corr:12.6f}{status_corr:>8}"
            f"{py_paper:12.4f}{py_corr:12.4f}"
        )

    print("-" * len(header))
    print(f"* y columns are informational only — see docstring / README.md")
    print()
    print(f"Corrected-conversion x-results: {passed} passed, {failed} failed")
    print(
        "Expected outcome: 'corrected' x PASSes at every point (machine "
        "epsilon, per opencv_openlensio_full_pipeline_pixel_corrected); "
        "'paper' x FAILs at every point with nonzero tangential contribution "
        "(per opencv_openlensio_full_pipeline_pixel_iff's ws/w=fx requirement, "
        "which this real fixture does not satisfy)."
    )

    if failed > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
