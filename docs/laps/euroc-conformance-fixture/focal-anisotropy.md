# The fx ≠ fy Issue

## Computation (conditional on the Weak-tier full-array hypothesis in `sensor-acquisition-audit.md`)

Given `sx = sy = 0.006 mm/px` (MT9V034 pixel pitch, 6.0×6.0 µm, per the datasheet) and EuRoC cam0's `fx = 458.654 px`, `fy = 457.296 px`:

```
Fx = fx · sx = 458.654 × 0.006 = 2.751924 mm
Fy = fy · sy = 457.296 × 0.006 = 2.743776 mm
```

`Fx ≠ Fy`. Difference: `0.008148 mm` (≈0.30% relative to Fx). Recorded as-is — **not** averaged, not used to select one value, not attributed to noise, per the task's explicit instruction. Both values are conditioned on the same Weak-tier (inferred, not verified) physical-pixel-pitch assumption as the rest of the physical-dimension material; if that hypothesis is wrong, both `Fx` and `Fy` are wrong by the same unknown scale factor, but the *fact* that `Fx ≠ Fy` (i.e. `fx ≠ fy` in the underlying pixel calibration, which is scale-invariant) is independent of it — the calibration file itself directly reports `fx ≠ fy` in pixel units regardless of any physical-dimension question.

## Does the local OpenTrackIO/OpenLensIO material already answer this?

**Yes, substantially — `docs/specification-questions.md` SQ-CV-04 ("Single focal length F vs separate fx, fy") is already resolved, and it is the relevant existing entry.** No new SQ-CV entry is added by this task; the finding here is recorded as an application of SQ-CV-04 to a concrete real-world calibration, not a new open question.

`opencv_opentrackio_proofs/PrincipalPointConversion.lean` proves (theorem `single_focal_length_compatibility`, and the underlying `principal_point_conversion_2d_iff`) that OpenTrackIO's single scalar `F` exactly represents an OpenCV calibration's two axes **if and only if**:

```
(w / w_shader) · fx = (h / h_shader) · fy
```

where, per `docs/opentrackio-proof-summary.md` §2.1/§3.1, `w`/`h` are the sensor's *physical* (mm) width/height and `w_shader`/`h_shader` are the raster (pixel) width/height — i.e. `w/w_shader = sx` (mm/px pixel pitch), and the condition is exactly `fx·sx = fy·sy`, i.e. `Fx = Fy` in the notation above. This is a **necessary and sufficient**, machine-checked condition — not an invented reconciliation rule, not an averaging rule, not a square-pixel assumption. The theorem does not pick a value when the condition fails; it only characterizes exactly when a single `F` is exact.

### What is genuinely still open

`single_focal_length_compatibility` tells you *whether* a single `F` is exact — it does **not** define what a producer/consumer should do **when it isn't** (EuRoC cam0's case, since `Fx ≠ Fy` above). No averaging, fallback, or "closest F" policy is proved, specified, or referenced anywhere found in this repo's `docs/` or `openlensio_semantics/`. This is a real gap, but it is a *sub-case of SQ-CV-04's already-open territory* (SQ-CV-04 proves the boundary condition; it was never claimed to resolve the non-exact case), not a distinct new specification question — so per the task instruction ("check whether it overlaps... before adding a new one"), **no new SQ-CV entry is added.** If a future task wants to track the "what happens when the exactness condition fails" question explicitly, it should be recorded as a sub-note under SQ-CV-04 rather than a new SQ-CV-0N, to avoid fragmenting the same underlying question across two entries.

### Any anamorphic/pixel-aspect parameter?

Not found in `openlensio_semantics/` (`LensSemantics.lean`, `ProjectionModel.lean`, `FovModel.lean`, `AngleOfView.lean` were grepped/skimmed for `focal`/`pixelPitch`/anamorphic-adjacent terms during this task; none define a second scalar or aspect-ratio correction alongside `F`). The model, as formalized in this repo, is a single-scalar-`F` model with no anamorphic escape hatch — consistent with `single_focal_length_compatibility` being stated as an exact-equality condition rather than always-satisfiable.

### Is the derivation x-derived only, or is there a separate y-relation?

There is a separate, explicitly proved y-relation: `principal_point_conversion_2d_iff` (theorem 3 in `PrincipalPointConversion.lean`) proves the 2D (x **and** y) case directly, by specializing the joint hypothesis at `(x'', 0)` and `(0, y'')` and reusing the 1D iff lemma on each axis independently. It is not an x-only derivation with y assumed symmetric by informal analogy — both axes are proved.
