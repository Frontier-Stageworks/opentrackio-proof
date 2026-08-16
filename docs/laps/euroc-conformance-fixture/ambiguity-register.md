# Ambiguity Register — EuRoC Conformance Fixture

Recorded before acting, per task instruction. Each item states the ambiguity, the decision taken (if any), and the evidence tier.

## AMB-EUROC-001: MT9V034 vs MT9M034

**Ambiguity**: `ethz-asl/maplab_rovio`'s `euroc_cam0.yaml` comment says "MT9M034"; ASL's own `visensor_node` wiki says "MT9V034" for the VI-Sensor hardware in general.
**Decision**: MT9V034. Evidence: ASL driver-repo wiki (near-primary) + exact resolution match to MT9V034's stated full array with no viable construction from MT9M034's array + global-shutter-vs-rolling-shutter engineering-plausibility argument. Full reasoning: `sensor-acquisition-audit.md` Part 1.
**Tier**: strong-but-not-single-source-authoritative (the single strongest possible source, the Nikolic et al. ICRA 2014 VI-Sensor paper, could not be fetched — AMB-EUROC-002).

## AMB-EUROC-002: Nikolic et al. ICRA 2014 paper unavailable

**Ambiguity/gap**: the paper that would most directly and authoritatively state the VI-Sensor's camera hardware was not accessible (IEEE Xplore paywalled; Semantic Scholar page returned no fetchable content; ResearchGate/other mirrors not pursued further after two failed attempts).
**Decision**: documented as a search failure per the task's stop condition, not silently worked around. Sensor identity rests on the three-part argument in AMB-EUROC-001 instead.
**Tier**: failure (for this specific source), does not by itself invalidate the sensor-identity conclusion given the alternative evidence.

## AMB-EUROC-003: Physical active area (4.512mm × 2.880mm)

**Ambiguity**: whether the mm dimensions are defensible fixture metadata.
**Decision**: computed and recorded, but tagged `"inferred"`, not `"verified"` — see AMB-EUROC-004 (the acquisition-mode question this depends on is itself Weak-tier).
**Tier**: Weak, per the task's own predefined tier taxonomy.

## AMB-EUROC-004: Crop / windowing / acquisition mode

**Ambiguity**: does EuRoC cam0's 752×480 correspond to MT9V034's full native array, unwindowed?
**Decision**: classified Weak (strongly supported by an elimination argument from the datasheet's own documented capability list, but no EuRoC-specific "full readout" statement found; `libvisensor`, the lowest-level driver that would set acquisition registers, could not be cloned in this session — see `investigation-log.md`).
**Tier**: Weak. Full reasoning: `sensor-acquisition-audit.md` Part 2.

## AMB-EUROC-005: Coefficient ordering

**Ambiguity**: the raw calibration array from `maplab_rovio`'s config is `[k1, k2, p1, p2, k3]` (5 elements, radtan/plumb_bob convention, with `k3 = 0.0` last) — a **different field order** than this repo's `InverseApproximation.Coeffs` structure, which is `⟨k1, k2, k3, p1, p2⟩` (k3 immediately after k1,k2, before p1,p2).
**Decision**: recorded explicitly to prevent a future task from mis-assigning `p1`'s numeric value into `Coeffs.k3` or vice versa by copying array position instead of matching by name. No assignment is made in this task (no fixture JSON generated — §7–9 not authorized). Any future instantiation must map by **name**, not by raw-array position: `k1=-0.28340811, k2=0.07395907, k3=0.0, p1=0.00019359, p2=1.76187114e-05`.
**Tier**: resolved (a bookkeeping ambiguity, not an evidentiary one).

## AMB-EUROC-006: U→D vs D→U direction

**Ambiguity**: which direction kalibr's radtan model computes, and whether that matches this repo's existing pipeline direction assumption.
**Decision**: kalibr's `distort()` (both in `RadialTangentialDistortion.hpp` and independently in `PinholeCameraGeometry.cpp`) computes **undistorted-normalised-in → distorted-normalised-out** (U→D) in closed form; `undistort()` computes the opposite direction via 5-iteration Gauss-Newton — no closed form. This matches `Pipeline/OpenCVModel.lean`'s documented U→D direction exactly, and reinforces (does not resolve) SQ-CV-07's observation that D→U has no closed form in a real, independently-written reference implementation, not merely as a modeling choice in this repo.
**Tier**: Strong — directly read from kalibr source, two independent implementations agree.

## AMB-EUROC-007: fx ≠ fy

**Ambiguity**: EuRoC cam0's `fx = 458.654 ≠ fy = 457.296`. No averaging, fx-only, fy-only, or square-pixel substitution performed.
**Decision**: both recorded; `Fx = 2.751924mm ≠ Fy = 2.743776mm` computed and both kept. See `focal-anisotropy.md`.
**Tier**: n/a (a fact, not an ambiguity requiring a choice) — the *what to do about it* question is the genuinely open part, addressed next.

## AMB-EUROC-008: Scalar physical focal length reconciliation

**Ambiguity**: OpenTrackIO's `pinholeFocalLength` is a single scalar; EuRoC cam0 has no single value that represents both axes exactly (`Fx ≠ Fy`, and `single_focal_length_compatibility` in `PrincipalPointConversion.lean` proves this is exactly the condition under which a single `F` fails).
**Decision**: not resolved in this task — no averaging/selection rule invented. Recorded as an application of the already-open remainder of SQ-CV-04 (see `focal-anisotropy.md`), not a new specification question.
**Tier**: open, pre-existing (SQ-CV-04's unresolved remainder).

## AMB-EUROC-009: Sensor raster vs. delivered/render raster

**Ambiguity**: `w_shader` (752px) in this repo's `PrincipalPointConversion.lean` model is the raster the calibration's `fx,fy,cx,cy` are defined over — this is unambiguously EuRoC's *delivered* image raster, confirmed regardless of the acquisition-mode question. It is only the *physical mm width `w`* derivation that additionally assumes `752px` also equals the *sensor's native* raster (the Weak-tier acquisition-mode hypothesis in AMB-EUROC-004). If that hypothesis is ever overturned, `w_shader=752` remains correct for all normalized/pixel-space work; only the mm-based `w`/`Fx`/`Fy` values would need revision.
**Decision**: keep these two roles explicitly distinct in any future fixture JSON — do not let a single field silently serve both purposes.
**Tier**: resolved (a modeling-clarity note, not an evidentiary gap).
