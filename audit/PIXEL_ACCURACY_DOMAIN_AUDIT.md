# Pixel-Accuracy Domain Audit

Adversarial review of `audit/CERTIFIED_NUMERICAL_INVERSION.md` and its Lean
declarations (`Pipeline/PixelIterationBounds.lean`), for two possible gaps:
(1) whether multiplying normalised-coordinate error by `fx` alone certifies the
**true 2D pixel distance** when `fx ≠ fy`, and (2) whether the numerical
cross-check's test points actually satisfy the Lean theorems' domain
hypotheses — plus a specific check on the reported 204-iteration TUM fr2
"full-image" case.

**This document does not modify, weaken, or delete anything in
`Pipeline/PixelIterationBounds.lean` or `audit/CERTIFIED_NUMERICAL_INVERSION.md`.**
All three original theorems there (`fr1_pixel_error_bound_N17`,
`fr2_pixel_error_bound_N26`, `kinect_pixel_error_bound_N59`) remain true,
unmodified, and exactly as strong as before. This document adds corrected
companion theorems (`Pipeline/PixelAccuracy2D.lean`, new file) and clarifies,
without retracting, the original document's claims.

| Task item | Finding | Disposition |
|---|---|---|
| 1. Does `fx·‖Δ‖` certify true 2D pixel distance? | **No, not in general** — only when `fx ≥ fy`. True for fr1, Kinect. **False in general for fr2** (`fy > fx`). | **Fixed**: new `max(fx,fy)`-based theorems added (§1). Iteration counts unchanged. |
| 2. Do the cross-check's test points satisfy the Lean domain hypothesis? | **No — 16–36% of the original naive samples, per camera, violate it.** | **Corrected**: domain-respecting cross-check re-run via rejection sampling (§2); original out-of-domain fraction quantified. |
| Also: does the N=204 "full-image capstone" satisfy the existence/convergence domain, or only injectivity? | **Only injectivity is full-image. The existence/buffer domain does *not* reach the image corners.** | **Clarified** (§3) — not a defect in any theorem, a mislabeling risk in prose. |

---

## 1. `fx` vs. true 2D pixel distance

### 1.1 The gap

`Pipeline/PixelIterationBounds.lean`'s three theorems each state
`fx * ‖Δ‖ < 1/1000`, where `Δ` is the normalised-coordinate error (a complex
number) and `fx` is the camera's horizontal focal length. The pinhole map is
`(px,py) = (fx·x+cx, fy·y+cy)`, so the **true** 2D pixel-space distance after
converting both coordinates is

```
pixel_dist = √((fx·Δ.re)² + (fy·Δ.im)²)
```

**not** `fx·‖Δ‖ = fx·√(Δ.re²+Δ.im²)`. These coincide only when `fx = fy`
(or when `Δ.im = 0`). In general,

```
√((fx·Δ.re)²+(fy·Δ.im)²) ≤ fx·‖Δ‖   holds  ⟺  fx ≥ fy
```

(when `fx < fy`, taking `Δ.re=0, Δ.im≠0` makes the left side `fy·|Δ.im|`,
strictly bigger than the right side `fx·|Δ.im|`). So `fx·‖Δ‖` is a valid
upper bound on the true 2D pixel distance **only when `fx ≥ fy`** — it is not
a general fact, and the original document's §3.3 ("exact, no approximation")
is correct about the *arithmetic* of the conversion but does not state this
`fx ≥ fy` precondition.

### 1.2 Checking the precondition against the actual camera intrinsics

| Camera | fx | fy | fx ≥ fy? | Original theorem valid as a 2D-distance bound? |
|---|---|---|---|---|
| TUM fr1 | 517.306408 | 516.469215 | **Yes** | **Yes** — `fr1_pixel_error_bound_N17` already bounds the true 2D distance. |
| TUM fr2 | 520.908620 | **521.007327** | **No** (`fy > fx`) | **No** — `fr2_pixel_error_bound_N26`'s `fx·‖Δ‖` does **not** rigorously bound the true 2D distance; it is a true statement about a different (single-axis-scaled) quantity. |
| Azure Kinect DK | 606.908447265625 | 606.661376953125 | **Yes** | **Yes** — `kinect_pixel_error_bound_N59` already bounds the true 2D distance. |

So the gap is real, but narrow: of the three original theorems, exactly
**one** (fr2) needed a different multiplier to honestly claim a 2D-distance
bound; the other two were already correct for that claim, just not framed
that way explicitly.

### 1.3 The fix: a `max(fx,fy)` bound, proved once, applied to all three

The always-valid bound, regardless of which of `fx,fy` is larger, is

```
√((fx·Δ.re)²+(fy·Δ.im)²) ≤ max(fx,fy) · √(Δ.re²+Δ.im²) = max(fx,fy) · ‖Δ‖
```

Proved as a standalone, general, pure-algebra lemma (no camera-specific facts)
in the new file `opencv_opentrackio_proofs/Pipeline/PixelAccuracy2D.lean`:

```lean
theorem pixel_dist2D_le_max_mul_norm (fx fy dx dy : ℝ) (hfx : 0 ≤ fx) (hfy : 0 ≤ fy) :
    Real.sqrt ((fx * dx) ^ 2 + (fy * dy) ^ 2) ≤ max fx fy * Real.sqrt (dx ^ 2 + dy ^ 2)
```

plus the complex-norm identity needed to connect it to the project's
`ℂ`-valued iteration-error theorems:

```lean
theorem complex_norm_eq_sqrt_re_im_sq (z : ℂ) : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2)
```

and three new, camera-specific, **corrected** 2D-pixel-distance theorems,
reusing the existing normalised-error machinery with no re-derivation of the
Banach/contraction facts:

```lean
theorem fr1_pixel_dist2D_bound_N17 (y : ℂ) (hy : ...) :
    Real.sqrt ((517.306408 * Δ.re)^2 + (516.469215 * Δ.im)^2) < 1/1000

theorem fr2_pixel_dist2D_bound_N26 (y : ℂ) (hy : ...) :
    Real.sqrt ((520.908620 * Δ.re)^2 + (521.007327 * Δ.im)^2) < 1/1000

theorem kinect_pixel_dist2D_bound_N59 (y : ℂ) (hy : ...) :
    Real.sqrt ((606.908447265625 * Δ.re)^2 + (606.661376953125 * Δ.im)^2) < 1/1000
```

(`Δ` abbreviates the same iteration-minus-true-fixed-point expression as the
original theorems; exact statements are in the Lean file.) Each proof:
instantiate `pixel_dist2D_le_max_mul_norm` at the camera's exact `fx,fy`,
simplify `max(fx,fy)` to whichever is larger by `norm_num`, and chain with
either the already-proved original theorem (fr1, Kinect — where
`max(fx,fy)=fx` so the original bound transfers directly) or directly with
`RDist_iteration_error_bound_tight_pos` (fr2 — where `max(fx,fy)=fy≠fx`, so
the original single-axis theorem cannot be reused as an intermediate step;
the `fy`-scaled bound is re-derived from the normalised-error theorem
instead, at the same `N=26`, with no change to the contraction/Banach part).

### 1.4 Iteration counts rechecked: unchanged

The question "does the corrected multiplier change how many iterations are
needed for <0.001 px?" was checked **before** writing any Lean, by direct
numerical comparison of `fx·bound` vs. `max(fx,fy)·bound` at each camera's
already-certified `N`:

| Camera | N | fx·bound | max(fx,fy)·bound | Still < 0.001 px? |
|---|---|---|---|---|
| TUM fr1 | 17 | 0.000993 px | 0.000993 px (fx is already the max) | Yes — unchanged |
| TUM fr2 | 26 | 0.000644 px | 0.000646 px (now scaled by fy, not fx) | Yes — margin shrinks negligibly, still comfortably `< 0.001` |
| Azure Kinect DK | 59 | 0.000884 px | 0.000884 px (fx is already the max) | Yes — unchanged |

**No camera's certified iteration count changes.** The fix is a correction to
theorem-statement rigor (what quantity is actually being bounded), not a
change to the practical N=17/26/59 results — confirmed by `norm_num` closing
all three corrected theorems in Lean, not just by the Python estimate above.

### 1.5 Build and axioms

```
$ lake build
Build completed successfully (8409 jobs).
```

```
#print axioms pixel_dist2D_le_max_mul_norm      -- propext, Classical.choice, Quot.sound
#print axioms complex_norm_eq_sqrt_re_im_sq     -- propext, Classical.choice, Quot.sound
#print axioms fr1_pixel_dist2D_bound_N17        -- propext, Classical.choice, Quot.sound
#print axioms fr2_pixel_dist2D_bound_N26        -- propext, Classical.choice, Quot.sound
#print axioms kinect_pixel_dist2D_bound_N59     -- propext, Classical.choice, Quot.sound
```

No `sorry`, no custom axioms, no `native_decide`/`unsafe`/`partial`.

---

## 2. Domain hypothesis vs. the numerical cross-check's test points

### 2.1 The gap

`CERTIFIED_NUMERICAL_INVERSION.md` §6 sampled 2000 ground-truth points `xu`
**uniformly in the full certified disk** `‖xu‖ ≤ R`, forward-distorted them to
get `y = RDist(θ, xu)`, then ran the iteration from `y` for the Lean-proved
`N` and compared to the certified bound. But the Lean theorems' actual
hypothesis is not `‖xu‖ ≤ R` — it is a hypothesis **on `y`**:

```
‖y‖ + MPertTightPos/Neg(...) ≤ R        i.e.        ‖y‖ ≤ Rb := R - MPert(R)
```

a strictly **smaller** "buffer disk" of radius `Rb < R` (this is the same
`Rb` distinction already established in `IMPROVED_REAL_CALIBRATION_BOUNDS.md`
and restated in `Pipeline/FullImageInjectivity.lean`'s own doc comment).
Sampling `xu` uniformly over the *full* `R`-disk and forward-distorting it
does **not** guarantee `‖y‖ ≤ Rb` — distortion can and does push some `y`
outside the buffer disk even when `xu` itself is a valid, in-range
undistorted point. §6 did not check this, so an unknown fraction of its 2000
samples per camera were run through the iteration (and compared against "the
certified bound") without actually satisfying that bound's hypothesis.

To be precise about what kind of error this is: it is **not** a soundness
violation of any Lean theorem (the theorems are universally quantified over
`y` satisfying the hypothesis, and remain true); it is a **methodological**
issue in the *informal numerical cross-check*, which implicitly suggested
every sampled comparison was testing "the certified case."

### 2.2 Quantifying the original sampling's domain violation

Reimplementing the exact forward map `RDist` and iteration map
`inverseStepRTight`/`inverseStepRTightNeg` from
`Pipeline/RationalDistortionBounds.lean` /
`Pipeline/TightBoundsNoDenominator.lean` /
`Pipeline/TightBoundsWithDenominator.lean` in Python (same recurrence, same
coefficients, double precision), and repeating §6's original sampling style
(`xu` uniform in the full `R`-disk, 2000 points, fixed seed) for each camera:

| Camera | R | Rb (buffer) | N | **out-of-domain samples / 2000** | max error, in-domain subset | max error, **out-of-domain** subset |
|---|---|---|---|---|---|---|
| TUM fr1 | 0.70 | 0.65482 | 17 | **346 (17.3%)** | 1.16×10⁻¹³ px | **1.47×10⁻¹⁰ px** |
| TUM fr2 | 0.75 | 0.70683 | 26 | **325 (16.3%)** | 1.19×10⁻¹³ px | 6.63×10⁻¹³ px |
| TUM fr2 (capstone, R=0.79) | 0.79 | 0.73089 | 204 | **399 (20.0%)** | 1.29×10⁻¹³ px | 1.19×10⁻¹³ px |
| Azure Kinect DK | 0.40 | 0.32495 | 59 | **724 (36.2%)** | 6.79×10⁻¹⁴ px | 7.53×10⁻¹⁴ px |

**16–36% of the original per-camera samples were outside the Lean theorems'
domain hypothesis** — not a small or negligible fraction. More strikingly,
for **TUM fr1**, the out-of-domain subset's worst measured error
(1.47×10⁻¹⁰ px) closely matches the order of magnitude of the *original*
document's reported worst-case figure ("**1.4×10⁻¹⁰ px**", §6's table) —
strong circumstantial evidence that the original §6 "measured iteration
error" number for fr1 was itself driven by a sample point that does **not**
satisfy the certified theorem's hypothesis, while the genuinely in-domain
points are three orders of magnitude more accurate (1.16×10⁻¹³ px). For fr2
and Kinect the in-domain/out-of-domain gap is much smaller (same order of
magnitude), so this specific overstatement risk is largely a TUM-fr1-specific
finding, not universal — but the underlying methodology gap (no domain check
at all) applied to every camera.

### 2.3 Corrected, domain-respecting cross-check

Rejection sampling (sample `xu` in the full `R`-disk; keep the sample only if
`y = RDist(θ,xu)` satisfies `‖y‖ ≤ Rb`; discard and resample otherwise) until
2000 genuinely certified points are collected per camera, then re-run both
comparisons from §6 — the iteration itself (same recurrence, same `N`, double
precision) and `cv2.undistortPoints` (OpenCV-Python 5.1.0, same version as
the original §6, fed the same normalised-space points via an identity camera
matrix so no additional calibration constants are needed):

| Camera | N | **certified** bound | measured iteration error (domain-respecting) | measured `cv2.undistortPoints` error (domain-respecting) |
|---|---|---|---|---|
| TUM fr1 | 17 | < 0.001 px | **1.18×10⁻¹³ px** | 1.76×10⁻⁵ px |
| TUM fr2 | 26 | < 0.001 px | **1.17×10⁻¹³ px** | 1.40×10⁻⁴ px |
| TUM fr2 (capstone, R=0.79) | 204 | < 0.001 px (numerically estimated only — see §3) | **1.17×10⁻¹³ px** | 7.16×10⁻⁴ px |
| Azure Kinect DK | 59 | < 0.001 px | **6.95×10⁻¹⁴ px** | 6.17×10⁻⁹ px |

All 2000/2000 samples per camera now genuinely satisfy the Lean theorems'
domain hypothesis. **Qualitative conclusion is unchanged from the original
§6** (certified bound sound and conservative; iteration far more accurate in
double precision than the certified bound requires) — but now on points that
actually are the certified case, not a mixture of certified and
non-certified ones. The `cv2.undistortPoints` errors are also smaller here
than §6's originally reported figures (fr1: 1.8×10⁻⁵ vs. 3.7×10⁻³; fr2:
1.4×10⁻⁴ vs. 2.0×10⁻²; Kinect: 6.2×10⁻⁹ vs. 4.5×10⁻⁸) — consistent with, not
contradicting, `REAL_CALIBRATION_VALIDATION.md`'s separate finding that
numerical accuracy (both this project's and OpenCV's) degrades toward the
image periphery; the buffer disk `Rb` is strictly smaller and farther from
that periphery than the full `R`-disk §6 sampled from.

### 2.4 Separating certified from merely empirical test points — summary

- **Certified test points**: any `y` with `‖y‖ ≤ Rb = R - MPert(R)`. The §5
  Lean theorems (and the new §1 2D-distance theorems) apply to **every** such
  point, not just the ones sampled here — the 2000-per-camera cross-check is
  a spot-check of a universally-quantified guarantee, not an exhaustive test.
- **Merely empirical points**: any `y` with `Rb < ‖y‖ ≤ R` (reachable by
  forward-distorting some in-range `xu`, but outside the theorem's
  hypothesis). The iteration can still be run on these in floating point —
  and in the data above it still converges extremely well — but **no Lean
  theorem backs that outcome**; it is observation, not guarantee, exactly
  per this document series' standing floating-point disclaimer.
- The original §6 table conflated the two without saying so. This document's
  §2.3 table is the corrected version restricted entirely to the first
  category; §2.2's table makes the size and effect of the conflation
  explicit rather than silently fixing it.

---

## 3. The TUM fr2 "full-image capstone" (N=204): injectivity vs. existence domain

### 3.1 The question

`CERTIFIED_NUMERICAL_INVERSION.md` §4's table includes a row "TUM fr2
(full-image capstone, R=79/100)" with N=204 for 0.001 px, and §7.4 describes
`R=79/100` as "the radius proved in `Pipeline/FullImageInjectivity.lean` to
certify the **entire** image rectangle." The task asked whether this
204-iteration case actually satisfies the **inverse-existence** domain
condition over the whole image, or whether this claim is only leaning on
**injectivity**.

### 3.2 What `Pipeline/FullImageInjectivity.lean` actually proves — and already says

Reading the file's own header comment (lines 17–27) and its two theorems:

- `fr2_image_rect_subset_cert_disk` + `fr2_full_image_injective`: every pixel
  in the full 640×480 image rectangle maps to a normalised point with
  `‖·‖ ≤ 0.79`, and `CVmap` is **injective** on that full-image set. This is
  a **100%-coverage** result, but only about injectivity (no two distinct
  pixels collide) — it says nothing about whether an inverse *exists and
  lands back in the certified region* for every one of those pixels.
- The file's own comment is explicit that the **existence** claim
  (`fr2_CVmap_invertible_capstone` / `RDist_exists_unique_preimage_tight_pos`)
  is restricted to "the smaller MPert-buffered sub-region," and warns against
  exactly the conflation this task asked about: *"Conflating 'injective on
  the full disk' with 'invertible-with-image-in-the-same-set on the full
  disk' would be the overclaim this file is designed to avoid."*

So the Lean code already carries the correct distinction. The risk is
**only** in `CERTIFIED_NUMERICAL_INVERSION.md`'s prose (§4's row label, §7.4's
"to certify the entire image rectangle" framing), which attaches the N=204
existence/iteration-convergence figure to the *injectivity* radius without
repeating the file's own caveat.

### 3.3 Checking the actual numbers

The iteration-existence/convergence guarantee (the one the N=204 figure is
actually about) requires `‖y‖ ≤ Rb := R - MPertTightPos(R)`. At `R=79/100`:

```
MPertTightPos(fr2 coefficients, R=0.79) = 0.05911   (already in §4's own table)
Rb = 0.79 - 0.05911 = 0.73089
```

fr2's actual image corners (640×480, fx=520.908620, fy=521.007327,
cx=325.141442, cy=249.701764 — same values `FullImageInjectivity.lean` uses),
converted to normalised coordinates, have maximum radius:

```
corner (0,0):     r = 0.78696   (the largest of the 4 corners)
corner (640,0):   r = 0.77139
corner (0,480):   r = 0.76485
corner (640,480): r = 0.74882
```

Since `Rb = 0.73089 < 0.74882` (the *smallest* corner radius), **every one of
the four image corners lies outside the existence/buffer disk** — the N=204
convergence guarantee does not reach any image corner, let alone the full
rectangle. This matches `IMPROVED_REAL_CALIBRATION_BOUNDS.md` §5a's own prior
finding for the same radius (`Rb≈0.731`, "giving ≈99.5% area coverage on the
existence side... not literally 100%") — this audit is not discovering a new
number, it is confirming that the existing ≈99.5%-coverage figure, not
"full-image," is the one that actually applies to the N=204 iteration count.

### 3.4 Disposition

- **No Lean theorem is wrong or overclaiming.** `FullImageInjectivity.lean`
  already states its own scope correctly, and no theorem anywhere asserts
  "N=204 iterations converge for every image pixel."
- **The gap is purely in `CERTIFIED_NUMERICAL_INVERSION.md`'s prose**: the
  row label "full-image capstone" and §7.4's "to certify the entire image
  rectangle" sentence are true of the *radius* `R=0.79` under the
  **injectivity** theorem, but the **N=204 iteration count that sits next to
  that label** is an **existence/convergence** fact, which only holds on the
  smaller, ≈99.5%-coverage buffer disk — a distinction the row does not make.
- Per the instruction to preserve existing valid theorems and documents,
  **`CERTIFIED_NUMERICAL_INVERSION.md` is left unmodified**; this section is
  the explicit correction/clarification, cross-referenced from here. Any
  future revision of that document should either (a) relabel the row
  "existence-domain capstone (≈99.5% image coverage)" rather than
  "full-image," or (b) add a footnote pointing to this section.
- **N=204 itself is not challenged** — it is still a valid (numerically
  estimated, not Lean-instantiated at that `N`, exactly as §9's original
  limitations already stated) iteration count for 0.001 px accuracy on the
  `Rb=0.73089` buffer disk, which is real and substantial (≈99.5% of the
  image area) even though it is not literally the whole image.

---

## 4. Files changed / added

- **Added**: `opencv_opentrackio_proofs/Pipeline/PixelAccuracy2D.lean` — the
  general `max(fx,fy)` 2D-distance lemma, the complex-norm identity, and
  three corrected camera-specific 2D-pixel-distance theorems. Builds clean,
  axiom-clean (§1.5).
- **Unmodified**: `Pipeline/PixelIterationBounds.lean`,
  `Pipeline/FullImageInjectivity.lean`, `audit/CERTIFIED_NUMERICAL_INVERSION.md`
  — all preserved exactly as before; nothing in them was weakened, and this
  document's findings do not require changing any of their theorem
  statements.
- No new axioms, no `sorry`/`admit`, no `native_decide`/`unsafe`/`partial`
  anywhere in the new file (confirmed both by `#print axioms`, §1.5, and by
  the project's standing forbidden-construct scan).
- The Python scripts used for §2's and §3's numerical checks were scratch
  tools for this audit (reimplementing the exact Lean-defined `RDist`/
  `inverseStepRTight`/`inverseStepRTightNeg` recurrences and sampling the
  disks as described); they are not committed, matching the convention
  already used for `CERTIFIED_NUMERICAL_INVERSION.md` §4 and §6's own
  Python-computed tables.

---

## 5. Remaining limitations (reported, not resolved)

- **Floating-point/production correctness is still not claimed** — §2's
  Lean/Python numbers are both evidence, not proof, of double-precision
  behavior; the binding disclaimer from `PixelIterationBounds.lean`'s header
  and `CERTIFIED_NUMERICAL_INVERSION.md` §2 is unchanged by this document.
- **The `max(fx,fy)` theorems are proved only at the same three `N` values
  as the originals** (17, 26, 59) — no new iteration-count search was
  performed; §1.4's table shows this was unnecessary (margins did not
  tighten enough to require a larger `N`), but a different camera with
  `fy ≫ fx` could in principle need a larger `N` under the honest 2D bound,
  which was not explored here since none of the three real cameras exhibit
  that.
- **The N=204 fr2 "capstone" case is still not Lean-instantiated at its own
  `N`** — same limitation already stated in `CERTIFIED_NUMERICAL_INVERSION.md`
  §9, unaddressed here.
- **This audit's domain-hypothesis fraction (16–36% out-of-domain) is
  specific to uniform sampling over the full `R`-disk** with the particular
  seed used; it is a property of the *sampling method* used in §6, not a
  universal percentage — a different (e.g. Gaussian, or edge-weighted)
  sampling distribution would show a different out-of-domain fraction, and
  no claim is made that 16–36% is somehow "the" out-of-domain rate for these
  cameras in general.
- **SQ-CV-07 and native OpenLensIO D→U interoperability** — untouched, as in
  every prior document in this series.
