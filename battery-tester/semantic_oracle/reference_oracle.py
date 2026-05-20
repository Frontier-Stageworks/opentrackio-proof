"""
reference_oracle.py — OpenLensIO semantic reference oracle (Python)

Independent Python implementation of the OpenLensIO v1.0.1 mathematical model.
This matches the Float definitions in ExecutableSemanticOracle.lean (OL-14) exactly.

NOT a verified proof. Serves as a cross-check oracle for differential testing.
Domain references: OpenLensIO v1.0.1 PDF, sections noted per function.
"""

from __future__ import annotations

import math


DOMAIN_TOLERANCE = 1e-10


# ─── Coordinate types ────────────────────────────────────────────────────────

def sensor_radius(ex: float, ey: float) -> float:
    """§1.1: r = sqrt(ε_x² + ε_y²)"""
    return math.sqrt(ex ** 2 + ey ** 2)


# ─── Radial polynomial — §4.1 Eq (17) ───────────────────────────────────────

def radial_term(k: list[float], r: float) -> float | None:
    """
    R = (1 + k1*r² + k3*r⁴ + k5*r⁶) / (1 + k2*r² + k4*r⁴ + k6*r⁶)

    Returns None if |denominator| < DOMAIN_TOLERANCE (domain failure).
    k = [k1, k2, k3, k4, k5, k6]
    """
    k1, k2, k3, k4, k5, k6 = k
    r2 = r ** 2
    r4 = r2 ** 2
    r6 = r2 * r4
    denom = 1.0 + k2 * r2 + k4 * r4 + k6 * r6
    if abs(denom) < DOMAIN_TOLERANCE:
        return None
    return (1.0 + k1 * r2 + k3 * r4 + k5 * r6) / denom


# ─── Brown-Conrady component form — §4.1 Eq (16) ────────────────────────────

def undistort_x(p: list[float], ex: float, ey: float, r: float, R: float) -> float:
    """U_x = R·ε_x + 2·p1·ε_x·ε_y + p2·(r² + 2·ε_x²)"""
    p1, p2 = p
    return R * ex + 2.0 * p1 * ex * ey + p2 * (r ** 2 + 2.0 * ex ** 2)


def undistort_y(p: list[float], ex: float, ey: float, r: float, R: float) -> float:
    """U_y = R·ε_y + p1·(r² + 2·ε_y²) + 2·p2·ε_x·ε_y"""
    p1, p2 = p
    return R * ey + p1 * (r ** 2 + 2.0 * ey ** 2) + 2.0 * p2 * ex * ey


def undistort_point(
    k: list[float], p: list[float], eps: tuple[float, float]
) -> tuple[float, float] | None:
    """
    U(ε) — undistortion function (OL-07).
    Returns None if radial denominator is near zero.
    """
    ex, ey = eps
    r = sensor_radius(ex, ey)
    R = radial_term(k, r)
    if R is None:
        return None
    return (undistort_x(p, ex, ey, r, R), undistort_y(p, ex, ey, r, R))


# ─── Projection and FOV forms — §2 Eq (4), §3 Eq (10) ───────────────────────

def undistort_from_distorted(
    k: list[float], p: list[float],
    eps_d: tuple[float, float],
    dc: tuple[float, float],
    dp: tuple[float, float],
) -> tuple[float, float] | None:
    """
    Eq (4): ε_u = U(ε_d − ΔC − ΔP) + ΔC + ΔP

    Shifts ε_d by −ΔC−ΔP, applies U, shifts back.
    Returns None on domain failure.
    """
    shifted = (eps_d[0] - dc[0] - dp[0], eps_d[1] - dc[1] - dp[1])
    u = undistort_point(k, p, shifted)
    if u is None:
        return None
    return (u[0] + dc[0] + dp[0], u[1] + dc[1] + dp[1])


def fov_undistort_from_distorted(
    k: list[float], p: list[float],
    eps_d: tuple[float, float],
    dc: tuple[float, float],
) -> tuple[float, float] | None:
    """
    Eq (10): ε'_u = U(ε'_d − ΔC) + ΔC  (FOV form — no ΔP)

    Returns None on domain failure.
    """
    shifted = (eps_d[0] - dc[0], eps_d[1] - dc[1])
    u = undistort_point(k, p, shifted)
    if u is None:
        return None
    return (u[0] + dc[0], u[1] + dc[1])


# ─── Shader coordinate conversion — §4.2 Eq (18) ────────────────────────────

def to_shader_coords(
    w: float, h: float, wshader: float, p: tuple[float, float]
) -> tuple[float, float]:
    """ε_shader = (wshader·ε_x/w + wshader/2, wshader·ε_y/h + wshader/2)"""
    return (
        wshader * p[0] / w + wshader / 2.0,
        wshader * p[1] / h + wshader / 2.0,
    )


def from_shader_coords(
    w: float, h: float, wshader: float, q: tuple[float, float]
) -> tuple[float, float]:
    """Inverse of Eq (18): mm from shader coords"""
    return (
        w * (q[0] - wshader / 2.0) / wshader,
        h * (q[1] - wshader / 2.0) / wshader,
    )


# ─── Angle of view — §2 Eq (6), §3.1 Eq (14) ────────────────────────────────

def angle_of_view(F: float, r_u: float) -> float:
    """α = 2 · arctan(r_u / F)"""
    return 2.0 * math.atan(r_u / F)


def fov_angle_from_width(F: float, w: float) -> float:
    """θ = 2 · arctan(w / (2F))"""
    return 2.0 * math.atan(w / (2.0 * F))
