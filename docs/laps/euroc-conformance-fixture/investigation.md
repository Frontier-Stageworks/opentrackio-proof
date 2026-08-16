# EuRoC Conformance Fixture — Investigation (§0–6)

Task slug: `euroc-conformance-fixture`. Large/investigation task, no Lean proof output — see LAPS GATE emitted at task start. This document covers §0–6 only; §7–9 (fixture generation, reference points, diagnostics) are conditional on the qualification decision in §6 and have **not** been attempted, per the task's explicit checkpoint.

Provenance detail: `provenance.md`. Sensor identity/acquisition-mode detail: `sensor-acquisition-audit.md`. Focal-length detail: `focal-anisotropy.md`. All ambiguities: `ambiguity-register.md`. Full search trail: `investigation-log.md`.

## §1 — The exact EuRoC/Kalibr cam0 calibration

| Field | Value |
|---|---|
| Dataset / camera | EuRoC MAV, cam0 |
| Resolution | 752 × 480 |
| Distortion model | "radtan" (kalibr) / "plumb_bob" (ROS convention) — both name the same 4-parameter Brown-Conrady model |
| Coefficient order (raw array) | `[k1, k2, p1, p2, k3]` = `[-0.28340811, 0.07395907, 0.00019359, 1.76187114e-05, 0.0]` |
| fx, fy | 458.654, 457.296 (px) |
| cx, cy | 367.215, 248.375 (px) |
| Source | `ethz-asl/maplab_rovio/cfg/euroc_cam0.yaml`, cross-corroborated by independent downstream repos (see `provenance.md`) |
| Provenance tier | strongly-corroborated secondary, **not** directly-verified against ASL's own original calibration archive (unreachable in this session — see `provenance.md`) |

**k3 = 0** — the calibration uses only the 2-term radial polynomial (`k1·r² + k2·r⁴`), not a 3rd-order term. This maps cleanly onto `InverseApproximation.Coeffs.k3 = 0` without truncation.

### Kalibr source trace — confirms the forward mapping and the direction

Two independent implementations inside kalibr agree exactly:

**`aslam_cv/aslam_cameras/include/aslam/cameras/implementation/RadialTangentialDistortion.hpp`, `distort()` (lines 4–25)**:
```cpp
rho2_u = mx2_u + my2_u;                                 // r² on the normalised plane
rad_dist_u = _k1*rho2_u + _k2*rho2_u*rho2_u;             // k1·r² + k2·r⁴
y[0] += y[0]*rad_dist_u + 2*_p1*mxy_u + _p2*(rho2_u + 2*mx2_u);
y[1] += y[1]*rad_dist_u + 2*_p2*mxy_u + _p1*(rho2_u + 2*my2_u);
```
This is the standard forward Brown-Conrady map: **undistorted normalised coordinate in, distorted normalised coordinate out** (the `_u` suffix in every intermediate variable literally denotes "undistorted"). It is applied on the normalised plane, before intrinsics — the same convention as `opencv_opentrackio_proofs/Pipeline/OpenCVModel.lean`'s `distortXCV`/`distortYCV` and `inverse_approximation/InverseApproximation.lean`'s `Φ`/`D`.

**`aslam_cv/aslam_cameras/src/PinholeCameraGeometry.cpp`, `distortion()` (lines 92–111)**: a second, independently-written implementation of the identical formula inside the pinhole-camera class itself (not merely calling the distortion class) — same equations, same variable-naming convention (`mx_u`, `my_u`, `_u` for undistorted).

**Inverse direction has no closed form in kalibr's own reference implementation.** `RadialTangentialDistortion::undistort()` (lines 67–100) and `PinholeCameraGeometry::undistortGN()` (lines 145–175) both solve the inverse (distorted→undistorted, "D→U") problem via a 5-iteration Gauss-Newton loop on the 2×2 forward Jacobian — not a closed form. This is independent, real-world corroboration (not merely a modeling choice made in this repo) of `docs/limitations.md`/SQ-OL-03's observation that the general Brown-Conrady inverse has no closed form.

## §2 — Sensor identity

**MT9V034.** Full evidence and the documented MT9M034 contradiction: `sensor-acquisition-audit.md` Part 1. Summary: ASL's own `visensor_node` wiki names MT9V034 directly (near-primary); the resolution `752×480` is an exact match to MT9V034's stated full/native array with no clean construction from MT9M034's `1280×960` array; MT9V034 is global-shutter (matches a "synchronized... accurate real-time SLAM" system), MT9M034 is rolling-shutter. A contradictory comment in a downstream `maplab_rovio` config ("MT9M034") is recorded, not silently discarded — this is exactly the naming confusion the task anticipated.

## §3 — Acquisition-mode provenance (the gating step)

**Weak** — per the task's own predefined tiers. Full reasoning: `sensor-acquisition-audit.md` Part 2. Summary: the MT9V034 datasheet (primary, full text obtained) states `752×480` is both the sensor's "Full Resolution"/"Active Pixels" *and* its documented default output mode, and its own windowing/binning features only ever produce *smaller* formats — so no documented MT9V034 configuration other than full, unwindowed readout produces exactly `752×480`. This is a real constraint, not mere coincidence-of-numbers, but no source found in this session makes an EuRoC-specific "full array, unwindowed" statement, and the lowest-level driver (`libvisensor`) that might contain one could not be inspected (2 failed clone attempts). Physical dimensions `4.512mm × 2.880mm` are therefore **not promoted to verified fixture metadata** in this task.

## §4 — fx ≠ fy

Full detail: `focal-anisotropy.md`. `Fx = fx·sx = 2.751924mm`, `Fy = fy·sy = 2.743776mm` (both conditioned on the Weak-tier pixel-pitch hypothesis from §3) — recorded as-is, not averaged or selected between. The repo's own `docs/specification-questions.md` SQ-CV-04 already proves the exact-representability condition (`single_focal_length_compatibility`: single `F` is exact iff `Fx = Fy`) — EuRoC cam0 fails it, as expected for a real calibration. No averaging/reconciliation rule is defined anywhere in this repo for the failing case; that remainder is recorded as part of SQ-CV-04's existing open territory, not a new SQ-CV entry (it overlaps). No anamorphic/pixel-aspect escape hatch exists in `openlensio_semantics/`. The y-axis relation is separately proved (`principal_point_conversion_2d_iff`), not assumed by x-only analogy.

## §5 — Compatibility with the existing proof model

No Lean code written or modified in this section — identification only, per task instruction.

| Aspect | EuRoC cam0 | Existing model | Compatible? |
|---|---|---|---|
| Radial form | polynomial, 2 active terms (`k1r²+k2r⁴`, `k3=0`) | `InverseApproximation.radial`: polynomial `k1r²+k2r⁴+k3r⁶` (Coeffs) | **Yes**, directly — set `k3=0` |
| Radial form (Pipeline) | same | `Pipeline/OpenCVModel.lean` `distortXCV`/`distortYCV`: **rational** `(1+k1r²+k2r⁴+k3r⁶)/(1+k4r²+k5r⁴+k6r⁶)` | **Yes**, degenerates exactly to polynomial when `k4=k5=k6=0` |
| Tangential form | standard Brown `2p1xy+p2(r²+2x²)` / `p1(r²+2y²)+2p2xy` | `Φ` and `distortXCV`/`distortYCV` use the identical formula | **Yes**, exact match, confirmed by direct comparison against kalibr's `distort()` |
| Direction | U→D closed form (§1) | `Coeffs`/`Φ`/`D`, `distortXCV`/`distortYCV` are all documented U→D | **Yes** |
| fx ≠ fy | 458.654 ≠ 457.296 | `PrincipalPointConversion.lean` theorems take `fx`,`fy` as independent parameters, never assume equality | **Yes** — no modification needed; EuRoC is in fact a natural non-trivial witness that `single_focal_length_compatibility`'s condition can fail for a real calibration |
| Principal point offset | `cx=367.215 ≠ w/2=376`, `cy=248.375 ≠ h/2=240` | `PrincipalPointConversion.lean` takes `cx`,`cy` as free parameters | **Yes** |
| Image dimensions | 752×480 | free `w`,`h`/`w_shader`,`h_shader` parameters | **Yes** |
| Coefficient ordering | raw array `[k1,k2,p1,p2,k3]` | `Coeffs` field order `⟨k1,k2,k3,p1,p2⟩` | **Yes, but must map by name, not array position** — recorded as AMB-EUROC-005 |

**No theorem in `InverseApproximation.lean`, `PrincipalPointConversion.lean`, or `Pipeline/OpenCVModel.lean` requires modification to accept EuRoC cam0's numbers.** This is a genuinely clean structural fit: every hypothesis EuRoC's calibration would need to satisfy (nonzero image dimensions, `fx`/`fy` free, `k4=k5=k6=0` for the rational model to degenerate) is already exactly how these theorems are stated — nothing about EuRoC's specific numeric values was needed to reach this conclusion, only its *shape* (4-parameter radtan, U→D, no assumed axis symmetry).

## §6 — Qualification decision

**Qualified normalized/pixel fixture only.**

Justification against the three offered categories:

- **Not** "Qualified full metric fixture": that tier requires defensible evidence for *all* of {real calibration, Brown-Conrady semantics, exact raster dimensions, physical active dimensions, acquisition mode, coefficient provenance}. Two of those are not at the required bar: physical active dimensions/acquisition-mode is Weak/inferred (§3), and coefficient provenance rests on strongly-corroborated secondary sources rather than a directly-verified original ASL file (§1/`provenance.md`).
- **Not** "Not suitable": the calibration's *shape* (a real, standard, polynomial Brown-Conrady radtan model, U→D, with independently-corroborated numeric values) is well established, and its semantics were confirmed against kalibr's actual executable source code (§1) — this is a materially real fixture, not a fabricated or unverifiable one.
- **Matches** "Qualified normalized/pixel fixture only": calibration valid (raster dimensions exact and multiply-corroborated, distortion coefficients and model shape confirmed against primary kalibr source), but physical mm dimensions are not strongly established — exactly this tier's description.

Physical dimensions (`4.512mm × 2.880mm`, `Fx`/`Fy`) **may** still be recorded in a future fixture, but only with an explicit `"inferred"` status flag (not `"verified"`) — consistent with how this repo's `battery-tester/opencv_cross_check/` was framed as illustrative rather than as conformance evidence.

---

## Final report

1. **Is EuRoC cam0 definitively MT9V034-based?** Strongly supported, not from a single definitive citation. ASL's own driver wiki names it directly; the resolution and shutter-type arguments independently corroborate; the one paper that would likely settle it definitively (Nikolic et al. ICRA 2014) could not be accessed. A contradictory "MT9M034" comment in a downstream config is documented and not treated as authoritative.

2. **Is 752×480 definitively the full physical active area?** No — Weak/inferred. It matches MT9V034's stated full/native array and default output mode exactly, and no documented MT9V034 configuration other than full readout produces that exact resolution, but no EuRoC-specific "unwindowed capture" statement was found, and the lowest-level driver that might contain one (`libvisensor`) could not be inspected in this session.

3. **Can 4.512×2.880mm be defensibly used?** Not as verified/authoritative fixture metadata. It can be used as a disclosed, `"inferred"`-tagged illustrative value, not as evidence for a rigorous full-metric conformance claim.

4. **What exact Brown-Conrady coefficients/semantics does the calibration use?** `k1=-0.28340811, k2=0.07395907, k3=0 (unused), p1=0.00019359, p2=1.76187114e-05`, standard 4-parameter polynomial radtan/plumb_bob, applied on the normalised image plane, undistorted→distorted (U→D) direction, confirmed against kalibr's own forward-distortion source code (two independent implementations agree). The inverse (D→U) has no closed form in kalibr's own reference implementation either (5-iteration Gauss-Newton).

5. **What physical focal lengths do fx/fy imply?** `Fx = 2.751924mm`, `Fy = 2.743776mm` (conditional on the Weak-tier pixel-pitch hypothesis) — a genuine, non-averaged, ≈0.30%-relative anisotropy.

6. **Can a single OpenTrackIO `pinholeFocalLength` represent the calibration exactly?** No. `Fx ≠ Fy`, and this repo's own `single_focal_length_compatibility` theorem proves that condition is exactly what makes exact single-`F` representation fail.

7. **If not, does the spec define reconciliation?** No averaging/selection/reconciliation rule was found anywhere in this repo's `docs/` or `openlensio_semantics/`. `single_focal_length_compatibility` (SQ-CV-04, already resolved) proves the *boundary condition* only; the "what to do when it fails" question remains open, recorded as part of SQ-CV-04's existing open remainder, not a new specification question.

8. **Suitable for**: normalized/pixel testing — **yes**, cleanly, no theorem modification needed (§5). mm↔pixel testing — only with the physical dimensions explicitly disclosed as inferred, not verified. Full OpenCV→OpenTrackIO conformance testing — not with a defensible physical-metric claim at this evidence tier; would additionally need to confront the unresolved single-`F` question (point 7) even if physical dimensions were verified.

9. **What ambiguity remains before this can be a real-camera end-to-end fixture?** (a) direct confirmation from ASL's own original calibration archive rather than corroborated downstream copies; (b) an explicit, EuRoC-specific acquisition-mode statement (ideally from `libvisensor` register-configuration code or the Nikolic et al. paper, neither accessible in this session); (c) a decided policy (upstream, not invented here) for what an OpenTrackIO producer should do when `fx ≠ fy` exactly. Full list with tiers: `ambiguity-register.md`.

## Stop

Per the task's checkpoint instruction: stopping here. §7–9 (fixture JSON generation, reference-point computation, oracle cross-checks) are not attempted and require explicit authorization to proceed, given the qualification tier landed at "normalized/pixel fixture only" rather than "full metric fixture."
