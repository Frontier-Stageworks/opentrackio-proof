#!/usr/bin/env python3
"""
battery-tester/semantic_oracle/run.py
Semantic differential test runner for the OpenLensIO oracle.

Runs the Python reference oracle (reference_oracle.py) on all fixtures in
fixtures.json and compares results against expected outputs (which match the
Lean Float oracle from ExecutableSemanticOracle.lean, verified in OL-14).

BLOCKER NOTE: Full differential testing against Mo-Sys C++ and CamDKit is
blocked — neither implementation provides an undistort math function. See
proof-capsule.md OL-15 for details. This script tests the Python reference
oracle for correctness against hand-computed expected values.
"""

import json
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from reference_oracle import (
    undistort_point,
    undistort_from_distorted,
    fov_undistort_from_distorted,
    to_shader_coords,
    from_shader_coords,
    angle_of_view,
    fov_angle_from_width,
)

TOLERANCE = 1e-10
FIXTURES_PATH = Path(__file__).parent / "fixtures.json"


def approx_eq(a: float, b: float, tol: float = TOLERANCE) -> bool:
    return abs(a - b) <= tol


def run_fixture(fx: dict) -> tuple[bool, str]:
    fn = fx["fn"]
    k = fx["k"]
    p = fx["p"]
    expected = fx["expected"]
    domain_valid = fx["domain_valid"]

    if fn == "undistort_point":
        result = undistort_point(k, p, tuple(fx["input"]))
    elif fn == "undistort_from_distorted":
        result = undistort_from_distorted(
            k, p, tuple(fx["eps_d"]), tuple(fx["dc"]), tuple(fx["dp"])
        )
    elif fn == "fov_undistort_from_distorted":
        result = fov_undistort_from_distorted(
            k, p, tuple(fx["eps_d"]), tuple(fx["dc"])
        )
    else:
        return False, f"Unknown function: {fn}"

    # Domain failure case
    if not domain_valid:
        if result is None:
            return True, "domain failure correctly returned None"
        return False, f"Expected None (domain failure), got {result}"

    # Normal case
    if result is None:
        return False, f"Expected {expected}, got None (unexpected domain failure)"

    rx, ry = result
    ex, ey = expected
    if approx_eq(rx, ex) and approx_eq(ry, ey):
        return True, f"({rx:.6f}, {ry:.6f})"
    return False, (
        f"MISMATCH: got ({rx:.10f}, {ry:.10f}), "
        f"expected ({ex:.10f}, {ey:.10f}), "
        f"delta=({abs(rx-ex):.2e}, {abs(ry-ey):.2e})"
    )


def main():
    fixtures = json.loads(FIXTURES_PATH.read_text())
    passed = 0
    failed = 0

    print(f"{'ID':<20} {'STATUS':<8} DETAIL")
    print("-" * 70)

    for fx in fixtures:
        fid = fx["id"]
        ok, detail = run_fixture(fx)
        status = "PASS" if ok else "FAIL"
        print(f"{fid:<20} {status:<8} {detail}")
        if ok:
            passed += 1
        else:
            failed += 1

    print("-" * 70)
    print(f"Results: {passed} passed, {failed} failed")

    if failed > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
