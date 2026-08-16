"""
reference_impl.py — OpenCV forward-distortion reference + paper/corrected
OpenTrackIO tangential-conversion parameter derivation.

Scope (see README.md in this directory): this is a scaffolding SANITY CHECK
on this repository's own formula transcription, and a source of one concrete
real-lens illustrative example. It is NOT a differential test against an
authoritative external implementation, and it does NOT adjudicate the F-vs-F²
tangential-conversion question — the Lean proofs in DistortionConversion.lean
/ DistortionConversionCorrected.lean / Pipeline/PixelIffCorrected.lean already
settle that exactly, for all inputs, not just the points exercised here.

Two pieces, each ported directly (not re-derived) from already-proven Lean:

1. The OpenCV forward Brown-Conrady formula, matching
   Pipeline/OpenCVModel.lean's distortXCV/distortYCV exactly:

       x'' = x' * R(r) + 2*p1*x'*y' + p2*(r² + 2*x'²)
       y'' = y' * R(r) + p1*(r² + 2*y'²) + 2*p2*x'*y'

   Deliberately NOT cv2/OpenCV's own undistort routines: those solve the
   inverse (distortion-removal) problem via numerical iteration, a different
   computation from the closed-form forward formula our proofs formalize.
   Using real cv2 here would introduce iterative-solver noise unrelated to
   what this scaffolding checks.

2. Parameter conversion (F, ΔPx, ΔPy, l1-l6, q1, q2), computed two ways:

       paper:     q1 = p1/F², q2 = p2/F²   (DistortionConversion.lean)
       corrected: q1 = p1/F,  q2 = p2/F    (DistortionConversionCorrected.lean)

   F, ΔPx, ΔPy, and the l1-l6 radial conversion are identical between the two
   modes — only the tangential q1/q2 formula differs, matching exactly what
   the two Lean files prove.

The OpenTrackIO side of the pixel pipeline reuses
battery-tester/semantic_oracle/reference_oracle.py's undistort_point
unmodified (it is already generic over k/p) rather than reimplementing it.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent / "semantic_oracle"))
from reference_oracle import undistort_point  # noqa: E402  (reused, not rewritten)


# ─── OpenCV forward Brown-Conrady ────────────────────────────────────────────
# Ported from Pipeline/OpenCVModel.lean:31-57 (distortXCV, distortYCV — named
# for direction: undistorted normalised coordinate in, distorted out).
#
# k convention here is OpenCV/DistortionConversion.lean naming:
#   k = [k1, k2, k3, k4, k5, k6], k1-k3 = radial numerator, k4-k6 = denominator.
# This is NOT the OpenTrackIO alternating convention (k1,k3,k5=num) used by
# reference_oracle.py — the two must not be mixed. (They coincide by
# construction for the OTI-side l1..l6 values computed by convert_params
# below, since DistortionConversion.lean's l1,l3,l5/l2,l4,l6 split already
# uses the OTI alternating convention.)

def opencv_radial_ratio(k: list[float], r: float) -> float:
    """R_cv(r) = (1 + k1r² + k2r⁴ + k3r⁶) / (1 + k4r² + k5r⁴ + k6r⁶)."""
    k1, k2, k3, k4, k5, k6 = k
    r2 = r * r
    r4 = r2 * r2
    r6 = r2 * r4
    num = 1.0 + k1 * r2 + k2 * r4 + k3 * r6
    den = 1.0 + k4 * r2 + k5 * r4 + k6 * r6
    return num / den


def distort_x_cv(k: list[float], p: list[float], xp: float, yp: float) -> float:
    """distortXCV (OpenCVModel.lean:31-39): R_cv·x' + 2p1x'y' + p2(r²+2x'²)."""
    p1, p2 = p
    r = math.sqrt(xp * xp + yp * yp)
    R = opencv_radial_ratio(k, r)
    return R * xp + 2.0 * p1 * xp * yp + p2 * (r * r + 2.0 * xp * xp)


def distort_y_cv(k: list[float], p: list[float], xp: float, yp: float) -> float:
    """distortYCV (OpenCVModel.lean:49-57): R_cv·y' + p1(r²+2y'²) + 2p2x'y'."""
    p1, p2 = p
    r = math.sqrt(xp * xp + yp * yp)
    R = opencv_radial_ratio(k, r)
    return R * yp + p1 * (r * r + 2.0 * yp * yp) + 2.0 * p2 * xp * yp


def opencv_pixel(
    fx: float, fy: float, cx: float, cy: float,
    k: list[float], p: list[float], xp: float, yp: float,
) -> tuple[float, float]:
    """OpenCV pixel output: u = fx*x'' + cx, v = fy*y'' + cy."""
    xpp = distort_x_cv(k, p, xp, yp)
    ypp = distort_y_cv(k, p, xp, yp)
    return fx * xpp + cx, fy * ypp + cy


# ─── Parameter conversion ────────────────────────────────────────────────────
# F, ΔPx: PrincipalPointConversion.lean:80-81 (principal_point_conversion_necessary).
# ΔPy: documented y-axis symmetric form (docs/limitations.md) — not part of the
#      formally proven x-only pipeline theorem; included for completeness.
# l1-l6: DistortionConversion.lean's radial_distortion_conversion (l = k/F^(2n)).
# q1,q2 "paper": DistortionConversion.lean's tangential_q1_conversion /
#                tangential_q2_conversion (q = p/F²).
# q1,q2 "corrected": DistortionConversionCorrected.lean's
#                tangential_q1_conversion_physical / _q2_conversion_physical
#                (q = p/F).

def convert_params(
    fx: float, fy: float, cx: float, cy: float,
    w: float, ws: float, h: float, hs: float,
    k_cv: list[float], p_cv: list[float],
    mode: str,
) -> tuple[float, float, float, list[float], list[float]]:
    """
    k_cv = [k1,k2,k3,k4,k5,k6] (OpenCV convention). p_cv = [p1,p2].
    mode: "paper" or "corrected".

    Returns (F, dpx, dpy, l_oti, q_oti) where l_oti = [l1,l2,l3,l4,l5,l6] is
    already in OTI alternating convention (l1,l3,l5=num; l2,l4,l6=den) —
    directly usable as the `k` argument to reference_oracle.undistort_point.
    """
    k1, k2, k3, k4, k5, k6 = k_cv
    p1, p2 = p_cv

    F = (w / ws) * fx
    dpx = (w / ws) * (cx - ws / 2.0)
    dpy = (h / hs) * (cy - hs / 2.0)

    l1 = k1 / F ** 2
    l3 = k2 / F ** 4
    l5 = k3 / F ** 6
    l2 = k4 / F ** 2
    l4 = k5 / F ** 4
    l6 = k6 / F ** 6

    if mode == "paper":
        q1 = p1 / F ** 2
        q2 = p2 / F ** 2
    elif mode == "corrected":
        q1 = p1 / F
        q2 = p2 / F
    else:
        raise ValueError(f"unknown mode: {mode!r} (expected 'paper' or 'corrected')")

    return F, dpx, dpy, [l1, l2, l3, l4, l5, l6], [q1, q2]


def oti_pixel_x(
    ws: float, w: float, F: float, dpx: float,
    l_oti: list[float], q_oti: list[float], xp: float, yp: float,
) -> float | None:
    """
    OpenTrackIO pixel x-output at screen point (F·x', F·y'), matching the RHS
    of opencv_openlensio_full_pipeline_pixel_iff / _corrected
    (Pipeline/PixelIff.lean, Pipeline/PixelIffCorrected.lean).

    Reuses reference_oracle.undistort_point unmodified: its (R·ε+tangential)
    output is exactly the bracketed OTI inner expression in those theorems.
    Returns None on radial-denominator domain failure (see reference_oracle's
    DOMAIN_TOLERANCE).
    """
    ex, ey = F * xp, F * yp
    u = undistort_point(l_oti, q_oti, (ex, ey))
    if u is None:
        return None
    ux, _uy = u
    return (ws / w) * (ux + dpx) + ws / 2.0


def oti_pixel_y(
    hs: float, h: float, F: float, dpy: float,
    l_oti: list[float], q_oti: list[float], xp: float, yp: float,
) -> float | None:
    """
    OpenTrackIO pixel y-output — informational only (see README.md). Not part
    of the formally proven x-only pipeline theorem; uses the documented
    symmetric y-axis form with the SAME single F as the x-axis (matching how
    Pipeline/PixelIff.lean scales both coordinates of the screen point by one
    scalar F). For a real calibration with fx ≠ fy this form cannot exactly
    reproduce the OpenCV y-pixel output regardless of the tangential
    conversion — see single_focal_length_compatibility in
    PrincipalPointConversion.lean and the note in README.md.
    """
    ex, ey = F * xp, F * yp
    u = undistort_point(l_oti, q_oti, (ex, ey))
    if u is None:
        return None
    _ux, uy = u
    return (hs / h) * (uy + dpy) + hs / 2.0
