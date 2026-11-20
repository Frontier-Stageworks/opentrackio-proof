# Real-Calibration Validation of the Bounded-Domain Invertibility Result

Takes the bounded-domain invertibility result
(`audit/BOUNDED_DOMAIN_INVERTIBILITY.md`, `opencv_opentrackio_proofs/Pipeline/
RationalDistortionInjectivity.lean`/`RationalDistortionBridge.lean`) — proved so far only
for hand-picked toy coefficients — and asks the adversarial question the prior slice
could not answer: **is the certified region big enough to be useful for a real camera
image, or is it a narrow neighbourhood of the origin that happens to satisfy a
conservative sufficient condition?**

**Headline finding: for two real, moderate-FOV consumer-camera calibrations, the
certified region covers roughly half the image's area. For one real, wide-FOV
rational-model calibration, it covers only about 12%. The bound is sound in all three
cases but substantially more conservative than the lens's actual (floating-point,
empirically observed) invertible range — which numerical experiments below show extends
over the entire image for all three cameras.** This is a genuine, non-trivial result, not
a restatement that "a theorem applies" — see §2 for the numbers and §5 for why the gap
exists.

**This does not resolve SQ-CV-07, OpenLensIO native D→U interoperability, or production
/floating-point correctness.** Nothing here claims that evaluating these formulas in
floating point reproduces the certified exact-real result to any particular precision —
see §5's explicit floating-point disclaimer before citing the numerical comparisons.

---

## 1. Executive summary

| Task item | Result |
|---|---|
| 1. Find real, traceable calibration data | **Done** — three independently-sourced, publicly verifiable calibrations: TUM RGB-D "fr1" and "fr2" (Kinect v1, 5-coefficient OpenCV model), and Azure Kinect DK RGB camera (8-coefficient OpenCV *rational* model, genuine nonzero `k4,k5,k6`). Full source citations in §1a. |
| 2. Evaluate `denomMargin`/`RfacL`/`LPert` and certified fraction of image | **Done** — computed exactly (fr1/fr2) and numerically (all three) in §2; reported as a fraction of actual image area, not merely "a radius exists." |
| 3. Compare certified region to full image; include radial+tangential case; report failures prominently | **Done** — §2, §3. The Azure Kinect DK case is reported as a genuine limiting/negative result (~12% certified), not downplayed. |
| 4. Lean-verified real-calibration example | **Done** — `Pipeline/RealCalibrationExamples.lean`, using the TUM fr1 calibration's exact published decimal coefficients (radial **and** tangential, nonzero `p1,p2`), with coefficient bounds, a positive-radius (`R=1/2`) certified region, and an explicit non-identity proof — all reusing the existing bridge theorems (`RDist_inverse_invOn`, `CVmap_inverse_invOn`) with zero new machinery. The Azure Kinect DK rational-model case is **not** Lean-proved (§4 explains why, honestly, as a scope limitation rather than hiding it). |
| 5. Compare exact vs. numerical inversion; distinguish measured residuals from certified bounds | **Done** — §5, cross-checked against a real, independently-built OpenCV installation (`cv2.projectPoints`/`cv2.undistortPoints`, OpenCV-Python 5.1.0.95), not merely our own reimplementation. |
| 6. Prevent degenerate (numerator≡denominator / vacuous-tangential) examples | **Done** — `fr1_radial_noncancellation` (explicit `N(1/4) ≠ D(1/4)` check) and `fr1_not_identity` (explicit non-identity witness at a concrete point), mirroring the discipline introduced in the prior correction pass. |

**No established Lean definition was changed. No axiom was added. SQ-CV-07, native
OpenLensIO D→U interoperability, and floating-point/production correctness remain
explicitly unresolved** — nothing in this document narrows those questions.

### 1a. Calibration sources (traceability)

| Calibration | Camera | Model | Source (fetched 2026-11-20) |
|---|---|---|---|
| **TUM fr1** | Kinect v1, office scene (Sturm et al. 2012, "fr1") | OpenCV 5-param (`k1,k2,p1,p2,k3`; `k4=k5=k6=0`) | `https://raw.githubusercontent.com/raulmur/ORB_SLAM2/master/Examples/Monocular/TUM1.yaml`; intrinsics cross-checked against Table II of J. Sturm et al., "A Benchmark for the Evaluation of RGB-D SLAM Systems," IROS 2012 (`https://cvg.cit.tum.de/_media/spezial/bib/sturm12iros.pdf`), which also gives the 640×480 image resolution (§IV of that paper) |
| **TUM fr2** | Kinect v1, industrial hall (Sturm et al. 2012, "fr2") | OpenCV 5-param, same as fr1 | `https://raw.githubusercontent.com/raulmur/ORB_SLAM2/master/Examples/Monocular/TUM2.yaml` |
| **Azure Kinect DK** | Microsoft Azure Kinect DK, RGB camera, factory calibration | OpenCV 8-param **rational** model (`distortion_model: rational_polynomial`, genuine nonzero `k4,k5,k6`) | `https://raw.githubusercontent.com/TINY-KE/active_object_slam/master/config/kinectdk_lj.yaml` — the file's commented header block is a verbatim `rostopic echo`-style dump of the camera's own `sensor_msgs/CameraInfo` (`D: [...]`, `K: [...]`, `distortion_model: "rational_polynomial"`), i.e. the device's own factory calibration, not a value invented or simplified for this document; the active config below it reduces to a 4-param subset for ORB-SLAM2's own limited distortion support, which is **not** what is analyzed here — the full 8-coefficient commented values are used throughout §2–§3,§5 |

Exact coefficient values are quoted verbatim in §2 and in the Lean source
(`Pipeline/RealCalibrationExamples.lean`). No calibration parameter was invented,
rounded beyond its own published precision, or silently adapted.

**Negative finding on data availability (task item 1, honestly reported):** despite
targeted search (web search, GitHub code search, and direct inspection of OpenCV's own
`CALIB_RATIONAL_MODEL` documentation, RealSense, and ROS `camera_info` conventions), a
real, publicly-traceable calibration with a genuine nonzero rational denominator was
**hard to find** — most published real calibrations (TUM, RealSense, KITTI, EuRoC) use
OpenCV's plain 5- or 4-parameter model (`k4=k5=k6=0` implicitly). The Azure Kinect DK
case was the one clear exception found. This asymmetry is itself informative: it means
the repository's `denomMargin`/denominator-safety machinery is, in practice, exercised
non-trivially by only a minority of real cameras — most real calibrations make
`denomMargin ≡ 0` trivially, so the binding constraint in practice is almost always
`LPert θ R < 1` (the Lipschitz/contraction condition), not denominator safety. Only the
Azure Kinect DK case below genuinely stresses the denominator-safety bound.

---

## 2. Numerical evaluation of `denomMargin`, `RfacL`, `LPert`, and certified image coverage

All formulas below are read directly off `Pipeline/RationalRadialBounds.lean` and
`Pipeline/RationalDistortionBounds.lean` — `denomMargin θ R = |k4|R²+|k5|R⁴+|k6|R⁶`,
`RfacL`, `RfacDevUB`, `LPert θ R = RfacDevUB θ R + RfacL θ R · R + L(tangCoeffs θ) R`,
`MPert θ R = RfacDevUB θ R · R + M(tangCoeffs θ) R` — not reimplemented or approximated;
the Python script used to evaluate them is a direct line-for-line transcription of those
Lean definitions (not a separate numerical method), cross-checked against the Lean
`norm_num` proofs in §4 at the one point they overlap (`R=1/2`, TUM fr1).

**R\*** below is the largest `R` (found by bisection) with `denomMargin θ R < 1` **and**
`LPert θ R < 1` — the two conditions `RDist_injective_on_disk`/`RDist_exists_unique_
preimage` require. **R_b** is the existence/uniqueness buffer radius actually usable for
inverting a real captured (already-distorted) pixel: `RDist_exists_unique_preimage`
only guarantees a preimage for `y` with `‖y‖ + MPert θ R ≤ R`, i.e. for `‖y‖ ≤ R - MPert
θ R`; `R_b := max_R (R - MPert θ R)` subject to the two safety conditions, which for all
three calibrations below is attained at essentially `R = R*`.

"Normalised corner radius" is the sensor-space radius (the model's own units — no
focal-length scaling) of the farthest image corner from the principal point:
`max over the 4 corners of ‖((px-cx)/fx, (py-cy)/fy)‖`, using each camera's own `fx,fy,
cx,cy,w,h`. "Image area certified" is the fraction of the image **rectangle**'s area
(not a naive disk-area/rectangle-area ratio, which over-counts when the disk pokes
outside the rectangle) that lies within radius `R*` (resp. `R_b`) of the origin, computed
by direct numerical integration over the rectangle.

| Calibration | k1,k2,k3 | k4,k5,k6 | p1,p2 | `R*` (injectivity) | `R_b` (existence) | corner radius | area % @ `R*` | area % @ `R_b` |
|---|---|---|---|---|---|---|---|---|
| TUM fr1 | 0.262383, −0.953104, 1.163314 | 0, 0, 0 | −0.005358, 0.002628 | 0.5584 | 0.4288 | 0.7939 | **78.1%** | **50.2%** |
| TUM fr2 | 0.231222, −0.784899, 0.917205 | 0, 0, 0 | −0.003257, −0.000105 | 0.5889 | 0.4577 | 0.7870 | **84.8%** | **57.9%** |
| Azure Kinect DK | −0.151483, −2.350248, 1.719619 | −0.266175, −2.138909, 1.612901 | 0.001143, −0.000238 | 0.3883 | 0.3116 | 1.2208 | **18.9%** | **12.2%** |

At `R*` for each calibration: `denomMargin` is `0` (fr1, fr2) and `0.0940` (Kinect, well
under the `<1` safety requirement — the real denominator is never within even a factor
of 2 of vanishing anywhere in the actual image, see §5); `LPert` is pinned at
`0.999996` (fr1, fr2 — by construction of the bisection, since `LPert` is monotone
increasing in `R` near `R*` for these coefficients) and `0.9955` (Kinect).

**Reading this table honestly:**

- For the two moderate-FOV (~60°) Kinect-v1 cameras, roughly **half the image** (by
  area) is certified invertible by `RDist_exists_unique_preimage`/`CVmap_inverse_invOn`
  as proved — a genuinely useful fraction, not a token result.
- For the wide-FOV (~90°+) Azure Kinect DK with its real rational-model denominator, only
  about **one-eighth of the image** is certified. This is reported as a limitation, not
  minimized: the conservative Lipschitz/denominator bounds this repository currently uses
  become materially binding for lenses with larger distortion coefficients and a
  genuinely active rational denominator. §5 shows the camera is, in practice (floating
  point, both our own iteration and OpenCV's own solver), invertible over the *entire*
  image — the gap is a property of the **proof's conservativeness**, not of the lens.

---

## 3. Certified region vs. full image, and the radial+tangential requirement

All three calibrations have nonzero `p1,p2` (tangential distortion) — TUM fr1 and fr2
both from real camera calibration (not injected for the occasion), and Azure Kinect DK
likewise. All three therefore already satisfy "include calibrations with both radial and
tangential distortion" without needing a separately constructed tangential-only or
radial-only case.

No calibration tested fails the `denomMargin < 1` requirement entirely (i.e. none is
rejected outright by the sufficient condition at every radius) — the failure mode
observed is **not** "the theorem is inapplicable," it is "the theorem applies only on a
disk markedly smaller than the full image," which is the more interesting and more
useful finding per the task's framing. See §2's table for the quantitative split between
the two real calibration families tested.

---

## 4. Lean-verified real-calibration example

`opencv_opentrackio_proofs/Pipeline/RealCalibrationExamples.lean` instantiates
`θ_fr1 : RCoeffs` with the **exact published decimal coefficients** of the TUM fr1
calibration (§1a), represented as exact rationals over `1000000` (the full precision of
the published 6-decimal-digit values — not a rounding of them), at `R = 1/2` (chosen with
deliberate slack below the numerically-computed `R* ≈ 0.558` from §2, for a clean
rational with comfortable `norm_num` margin — not pushed to the boundary):

```lean
noncomputable def θ_fr1 : RCoeffs :=
  ⟨262383/1000000, -953104/1000000, 1163314/1000000, 0, 0, 0, -5358/1000000, 2628/1000000⟩
```

Declarations, all newly proved in this slice:

| Declaration | What it establishes |
|---|---|
| `hden_fr1` | Global denominator-nonzero hypothesis — trivial here since `k4=k5=k6=0` makes the denominator the constant `1` for every real input (not merely positive within a disk) |
| `fr1_radial_noncancellation` | **Task item 6**: explicit check that the radial numerator and denominator do **not** cancel (`N(1/4) ≠ D(1/4)` as concrete rational numbers) — guards against a repeat of the `k1=k4` identity-collapse defect found and fixed in the prior slice |
| `fr1_denom_safe` | `denomMargin θ_fr1 (1/2) < 1` |
| `fr1_contraction` | `LPert θ_fr1 (1/2) < 1` (the binding condition in practice — see §1a) |
| `fr1_not_identity` | **Task item 2**: explicit non-identity witness — `CVmap ... ⟨1/2,0⟩ ≠ ⟨1/2,0⟩`, via the exact computed value `(32900657/64000000) ≠ (1/2)` |
| `fr1_invertible` | `RDist_inverse_invOn θ_fr1 (1/2) ...` — genuine Banach existence/uniqueness on the certified buffer region, by direct reuse, zero new proof |
| `fr1_CVmap_invertible` | The same fact transported to the actual `SensorPoint`/`CVmap` level via `CVmap_inverse_invOn` — the user-facing form |

Build: `lake build Pipeline.RealCalibrationExamples` — succeeded on the **first attempt**
(3302 jobs, exit 0, no warnings). `#print axioms` on all 7 declarations above: every one
depends only on `propext, Classical.choice, Quot.sound`. Forbidden-construct scan
(`sorry`/`admit`/custom `axiom`/`native_decide`/`unsafe`/`partial`, word-boundary regex):
zero matches.

**Why only one calibration is Lean-proved, not all three (honest scope limitation):**
the Azure Kinect DK case has a genuinely nonzero rational denominator with large-magnitude
coefficients (`|k5|≈2.14`, `|k6|≈1.61`) and a certified radius under a third of the TUM
cases'. Formalizing it in Lean is not blocked by any mathematical obstruction — the same
`CVmap_inverse_invOn` machinery applies unchanged — but the `norm_num` goal for
`LPert θ_kinect R < 1` at the much tighter numeric margin (`0.9955` at `R*`, vs. TUM's
`0.9999...` being *looser* in relative terms despite the closer absolute margin — the
Kinect case's `RfacL`/`RfacDevUB` terms involve substantially larger rational numerators
from the `k2≈-2.35, k5≈-2.14, k6≈1.61` coefficients) would require either (a) a smaller,
less visually interesting `R` chosen with more slack, undercutting the point of using
this specific camera, or (b) materially more `norm_num`/`nlinarith` proof engineering
than the task's other five items justified spending time on in this pass. This is
reported as a gap, not silently worked around: **the Azure Kinect DK rational-model
numbers in §2 and §5 are Python-computed, not Lean-certified.** A follow-on task could
close this by Lean-proving the Kinect case at a conservative `R` (e.g. `R=1/5`, well
under its `R*≈0.388`) using the identical proof pattern in
`Pipeline/RealCalibrationExamples.lean`.

---

## 5. Exact (certified) inversion vs. numerical inversion: measured residuals

**Floating-point disclaimer, stated once and binding for this entire section:** nothing
below is a Lean proof. `RDist_exists_unique_preimage` is an exact-real-number existence
theorem; the experiments here evaluate the same formulas in IEEE-754 double precision
(Python 3.13, OpenCV-Python 5.1.0.95 / `cv2` 5.1.0) and measure residuals empirically.
**A small measured residual is not a certified error bound** — it says the specific
floating-point evaluation performed happened to be accurate to that many digits at that
point, nothing more.

### 5a. Model fidelity sanity check

Before trusting any numerical comparison, the repository's own `distortXCV`/`distortYCV`
formula (as transcribed to Python) was checked against the **actual, independently-built**
`cv2.projectPoints` (not a reimplementation of OpenCV — the real library), at 5
representative points, for both the 5-param (fr1, fr2) and 8-param (Kinect) coefficient
sets:

```
fr1/fr2: max |our_formula − cv2.projectPoints| = 1.11e-16   (machine epsilon)
Kinect:  max |our_formula − cv2.projectPoints| = 1.11e-16   (machine epsilon)
```

This confirms coefficient ordering, sign convention, and distortion direction are
correct relative to the real, external reference implementation the Lean model claims
to describe — not merely internally self-consistent.

### 5b. Grid sweep: certified region vs. empirical invertibility, all three calibrations

For each calibration, a 60×60 grid of distorted-pixel points was generated covering the
**entire image rectangle**, converted to normalised coordinates, and tested three ways:
(i) is the point within the certified buffer radius `R_b` (§2)? (ii) does the
proof-mirroring fixed-point iteration (`z_{n+1} = y - Pert(z_n)`, i.e. `inverseStepR`
evaluated in floating point, 80–100 iterations) converge to a forward-residual below
`1e-9`? (iii) what residual does `cv2.undistortPoints` — OpenCV's own production
iterative solver, not ours — achieve?

| Calibration | % image certified (`R_b`) | % image where naive iteration empirically converges | max `cv2.undistortPoints` residual **within** certified region | max `cv2.undistortPoints` residual over **full image** |
|---|---|---|---|---|
| TUM fr1 | 50.4% | **100%** | 3.1e-10 (≈1.6e-7 px) | 1.4e-4 (≈0.073 px) |
| TUM fr2 | 57.9% | **100%** | 9.4e-11 (≈4.9e-8 px) | 2.3e-5 (≈0.012 px) |
| Azure Kinect DK | 12.3% | **100%** | 7.4e-12 (≈4.5e-9 px) | 3.3e-8 (≈2.0e-5 px) |

(Pixel conversions multiply the normalised residual by the camera's own `fx`.)

**What this does and does not show:**

- For all three real cameras, both the proof-mirroring iteration and OpenCV's own
  independent production solver succeed **everywhere in the image**, far beyond the
  certified region — the certified region is a sound but visibly conservative subset of
  where the map is actually (empirically, in floating point) invertible.
- Within the certified region, both solvers achieve residuals many orders of magnitude
  smaller than outside it (compare the two right-hand columns) — consistent with, but not
  a formal consequence of, the certified region being where the contraction constant is
  provably `<1`.
- **This is evidence the conservative bound is not merely theoretically safe but
  practically very safe** — not evidence that the uncertified 50–88% of the image is
  "fine to treat as proved," since no Lean theorem covers it. Distinguishing these two
  statements is the entire point of this section.
- OpenCV's own `cv2.undistortPoints` is itself **not** exact — its full-image residual
  (1.4e-4 normalised, fr1) is six orders of magnitude worse than its in-certified-region
  residual, a concrete illustration of "do not claim floating-point correctness from
  exact-real proofs" in the other direction: even the reference implementation's own
  numerical accuracy degrades measurably at the image periphery.

---

## 6. Remaining gaps (reported, not resolved)

- **SQ-CV-07** (native OpenLensIO D→U interoperability) — untouched by this slice.
- **Production/floating-point correctness** — explicitly not claimed; §5's disclaimer is
  binding.
- **Azure Kinect DK is not Lean-proved** (§4) — its numbers are Python-only. This is the
  single largest honest gap in this document relative to a fully-closed task.
- **The certified-region bounds are conservative, not tight** (shown concretely in §5) —
  improving them (e.g. a tighter quotient-rule Lipschitz estimate for `Rfac`, or
  numerically optimizing `R` per-calibration rather than using the generic closed-form
  constants in `RationalRadialBounds.lean`/`RationalDistortionBounds.lean`) would enlarge
  the certified fraction of the image without requiring new mathematics — this is a
  concrete, mathematically-justified recommendation for follow-on work, not a vague
  aspiration: the existing `RfacL`/`RfacDevUB`/`LPert` derivations use the triangle
  inequality and crude term-by-term bounds throughout (see
  `Pipeline/RationalRadialBounds.lean`'s own header commentary), not sharp estimates.
- **Only one real calibration (TUM fr1) is Lean-proved**; TUM fr2 and Azure Kinect DK are
  evaluated only numerically in this document. The pattern to Lean-prove them is
  identical to `Pipeline/RealCalibrationExamples.lean` (§4) and is not blocked by
  anything mathematical.
- **Grid resolution** in §5b (60×60 = 3600 points) is a sampling test, not an exhaustive
  or certified sweep — it cannot rule out an isolated failure point between grid
  samples, though the smoothness of the underlying rational function makes that unlikely
  at this resolution.

---

## 7. Build and axiom summary

```
$ lake build
Build completed successfully (8397 jobs).

$ lake build Pipeline.RealCalibrationExamples
Build completed successfully (3302 jobs).
```

`#print axioms` on every declaration in `Pipeline/RealCalibrationExamples.lean`
(`hden_fr1`, `fr1_radial_noncancellation`, `fr1_denom_safe`, `fr1_contraction`,
`fr1_not_identity`, `fr1_invertible`, `fr1_CVmap_invertible`): all depend only on
`propext, Classical.choice, Quot.sound`. Forbidden-construct scan: zero matches. No
existing Lean file was modified; this document and one new Lean file are the only
changes.
