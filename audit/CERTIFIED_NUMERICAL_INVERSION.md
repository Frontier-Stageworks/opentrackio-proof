# Certified Numerical Inversion: Pixel-Accurate Iteration Bounds

Extends the bounded-domain existence/injectivity results (`audit/REAL_CALIBRATION_VALIDATION.md`,
`audit/IMPROVED_REAL_CALIBRATION_BOUNDS.md`, `audit/REAL_CAMERA_CERTIFICATION_GAPS.md`) with a
**quantitative, kernel-checked PIXEL-accuracy guarantee for a finite number of iterations**
of the actual fixed-point solver these proofs' own Banach argument uses — not just "a
unique inverse exists," but "N=17/26/59 iterations of *this exact update rule* are
provably enough for sub-millipixel accuracy," for TUM fr1, TUM fr2, **and** Azure Kinect
DK.

**Headline result**: `fr1_pixel_error_bound_N17`, `fr2_pixel_error_bound_N26`,
`kinect_pixel_error_bound_N59` — three Lean theorems, each stating that after the stated
number of iterations of `z_{n+1} = y - Pert θ z_n` (starting from `z_0 = y`, the observed
distorted point), the pixel-space distance to the true (certified) undistorted point is
**strictly less than 0.001 pixels**, for the real published coefficients of each camera.
All three are axiom-clean (`propext, Classical.choice, Quot.sound` only).

**Keeps explicitly unresolved:** native OpenLensIO D→U interoperability (SQ-CV-07) and
production/IEEE-754 floating-point correctness — see §2's disclaimer, binding throughout.

---

## 1. Executive summary

| Task item | Result |
|---|---|
| 1. Quantitative N-iteration error bound, reusing bounded-domain contraction/inverse theorems | **Done** — `RDist_iteration_error_bound_tight_pos`/`_neg` (`Pipeline/IterationErrorBounds.lean`), derived by extracting a component of Mathlib's `ContractingWith.exists_fixedPoint'` that the EXISTING Banach proofs compute but discard (`⟨z, hzs, hfz, _, _⟩` — the 4th slot). No new contraction/Lipschitz fact was proved; only the conversion from Mathlib's `edist`/`ENNReal` rate bound to a `‖·‖`/`ℝ` one. |
| 2. Pixel-unit conversion; distinguish iteration error from rounding error | **Done** — §3 (exact affine scaling by `fx`, no approximation) and §2 (the floating-point disclaimer, stated once, binding for the whole document). |
| 3. Instantiate for fr2, and (feasible) fr1 and Kinect; find N for 0.1/0.01/0.001 px | **Done for all three** — §4's table gives N for all three thresholds; §5 Lean-verifies the 0.001px case for all three cameras (exceeding the task's "at least one" minimum). |
| 4. Compare with floating-point experiments and `cv2.undistortPoints`; no formal claim from numerics | **Done** — §6, using a real, independently-built OpenCV installation (not a reimplementation). |
| 5. Audit domain invariance, denominator safety, contraction hypotheses, hidden assumptions | **Done** — §7, including one genuine finding (§7.4): certified-coverage radius and iteration speed trade off against each other. |

**No existing theorem was weakened, no axiom was added**, and every non-identity/
denominator-safety check from prior passes is reused unchanged (§7.2–§7.3).

---

## 2. Mathematical vs. floating-point error — stated once, binding throughout

Every theorem in this document is an **exact-real-number** statement: `z_{n+1} = y -
Pert θ z_n` is evaluated as an identity between real (`ℝ`) and complex (`ℂ`) numbers, with
no rounding. **None of these theorems says anything about what happens when this same
recurrence is evaluated in IEEE-754 double precision.** Floating-point rounding error
accumulated over `N` iterations is a separate question this document does not formally
address — §6 reports a *numerical observation* (that double-precision evaluation of this
exact recurrence tracks the exact-real answer far more closely than the certified bound,
for the specific points tested) and explicitly labels it as such, not as a proof.

---

## 3. The N-iteration bound (task item 1) and its pixel conversion (task item 2)

### 3.1 Where the bound comes from — reused, not re-derived

Both `RDist_exists_unique_preimage_tight_pos` (`Pipeline/TightBoundsNoDenominator.lean`)
and `RDist_exists_unique_preimage_tight_neg` (`Pipeline/TightBoundsWithDenominator.lean`)
call

```lean
obtain ⟨z, hzs, hfz, _, _⟩ := hContract.exists_fixedPoint' hcomplete hMapsTo hys hedist
```

Mathlib's `ContractingWith.exists_fixedPoint'` actually returns **five** components, not
three — the full signature's conclusion is

```
∃ y ∈ s, IsFixedPt f y ∧ Tendsto (f^[·] x) atTop (nhds y)
  ∧ ∀ n, edist (f^[n] x) y ≤ edist x (f x) * K^n / (1 - K)
```

The existing proofs discard the last two (`_, _`) — they only needed existence and
uniqueness. **This file reconstructs the identical contraction** (same
`inverseStepRTight`/`inverseStepRTightNeg`, same `hMapsTo`, same `K`, same `hContract` —
built from the exact same reused lemmas:
`inverseStepRTight_maps_disk`/`inverseStepRTight_lipschitz`/`MPertTightPos_nonneg`/
`LPertTightPos_nonneg` for fr1/fr2, and their `_neg` analogues for Kinect) and this time
keeps the rate-bound component, converting it from `edist`/`ENNReal` to `‖·‖`/`ℝ` via one
new, general, purely-algebraic helper lemma (`ennreal_rate_bound_toReal`) and identifying
Mathlib's constructed fixed point with the project's own `RDistInvTight`/`RDistInvTightNeg`
via `ContractingWith.fixedPoint_unique'` — the exact same uniqueness lemma the original
proofs already use for their own `∃!` conclusion.

### 3.2 The two theorems

```lean
theorem RDist_iteration_error_bound_tight_pos
    (k1 k2 k3 p1 p2 R : ℝ) (hR : 0 ≤ R) (hdisc_h) (hdisc_g) (hdisc_psi) (hc)
    (hcontract : LPertTightPos k1 k2 k3 p1 p2 R < 1)
    (y : ℂ) (hy : ‖y‖ + MPertTightPos k1 k2 k3 p1 p2 R ≤ R) (n : ℕ) :
    ‖(inverseStepRTight k1 k2 k3 p1 p2 y)^[n] y
        - RDistInvTight k1 k2 k3 p1 p2 R hR hdisc_h hdisc_g hdisc_psi hc hcontract y‖
      ≤ MPertTightPos k1 k2 k3 p1 p2 R * (LPertTightPos k1 k2 k3 p1 p2 R) ^ n
          / (1 - LPertTightPos k1 k2 k3 p1 p2 R)
```

and `RDist_iteration_error_bound_tight_neg`, identical in shape for the genuine
rational-denominator (Kinect) case. **Starting point convention**: the iteration starts
at `z_0 = y` — the observed, already-distorted point itself — matching every concrete
undistort-by-iteration routine (including the one used for the floating-point
cross-checks in `REAL_CALIBRATION_VALIDATION.md` §5 and §6 below).

### 3.3 Pixel conversion — exact, no approximation

The pinhole relation `pixel = fx·normalised + cx` is **affine**, so for any two
normalised points `a, b`: `|pixel(a) - pixel(b)| = fx·|a - b|` exactly (the additive
constant `cx` cancels in the difference). Multiplying the bound above by `fx ≥ 0`
therefore converts it to an *exact* pixel-space bound with zero approximation error from
the conversion step itself:

```lean
have hmul := mul_le_mul_of_nonneg_left hb hfx  -- hb : the normalised-space bound
```

— this is the entirety of the "pixel conversion" step; all three theorems in §5 use it
identically.

---

## 4. Iteration counts for 0.1 / 0.01 / 0.001 px (task item 3)

Computed (Python, not Lean) from the exact closed-form bound
`N > log(threshold·(1-K)/(M·fx)) / log(K)`, using the same `MPertTightPos`/
`LPertTightPos`/`MPertTightNeg`/`LPertTightNeg` values already established in
`IMPROVED_REAL_CALIBRATION_BOUNDS.md`:

| Calibration | R | K (`LPert`) | M (`MPert`) | fx | N for 0.1 px | N for 0.01 px | N for 0.001 px |
|---|---|---|---|---|---|---|---|
| TUM fr1 | 7/10 | 0.5292 | 0.04518 | 517.306408 | 10 | 14 | **17** |
| TUM fr2 | 3/4 | 0.6429 | 0.04317 | 520.908620 | 15 | 20 | **26** |
| Azure Kinect DK | 2/5 | 0.8090 | 0.07505 | 606.908447 | 37 | 48 | **59** |
| TUM fr2 (full-image capstone, R=79/100) | 79/100 | 0.9375 | 0.05911 | 520.908620 | 132 | 168 | 204 |

The bolded N (0.001 px) is the one **Lean-verified** in §5 for each of the first three
rows. The capstone row is included deliberately — see §7.4.

---

## 5. Lean-verified sub-millipixel guarantees (task item 3, "success" criterion)

`Pipeline/PixelIterationBounds.lean`, three theorems, each `norm_num`-verified on the
exact published rational coefficients (same values as
`Pipeline/RealCalibrationExamplesImproved.lean`/`Pipeline/RealCalibrationKinectImproved.lean`
— no recalibration):

```lean
theorem fr1_pixel_error_bound_N17 (y : ℂ) (hy : ...) :
    (517306408/1000000 : ℝ)
      * ‖(inverseStepRTight ... y)^[17] y - RDistInvTight ... y‖ < 1/1000

theorem fr2_pixel_error_bound_N26 (y : ℂ) (hy : ...) :
    (520908620/1000000 : ℝ)
      * ‖(inverseStepRTight ... y)^[26] y - RDistInvTight ... y‖ < 1/1000

theorem kinect_pixel_error_bound_N59 (y : ℂ) (hy : ...) :
    (606908447265625/1000000000000 : ℝ)
      * ‖(inverseStepRTightNeg ... y)^[59] y - RDistInvTightNeg ... y‖ < 1/1000
```

Each proof: instantiate the §3.2 theorem at the stated `n`, multiply by `fx`, then
`norm_num` the resulting **fully concrete** rational inequality (`MPert·K^N/(1-K)·fx <
1/1000`, all four quantities exact rationals given the published coefficients and chosen
`R`). The Kinect case required `simp only [...]` rather than `unfold [...]` before
`norm_num` — `unfold` is single-pass and does not re-traverse a definition's own
unfolding (a quirk already documented in this repository's other Lean work;
`denomLBTightNeg` unfolds to an expression containing `MtightNeg`, which a single
`unfold` pass left un-reduced) — a tactic-level fix, not a mathematical one.

**Verified**: `#print axioms` on all three theorems shows only `propext, Classical.choice,
Quot.sound`.

---

## 6. Cross-check: certified bound vs. floating point vs. `cv2.undistortPoints` (task item 4)

2000 points sampled uniformly in the certified disk for each camera; `xu,yu` chosen,
forward-distorted via the real coefficients, then (a) run through the *exact same*
recurrence the Lean proof certifies, for exactly the Lean-proved `N`, in IEEE-754 double
precision, and (b) run through `cv2.undistortPoints` (OpenCV-Python 5.1.0, a real,
independently-built installation, not a reimplementation), measuring `max |result - xu,
yu| · fx` over all 2000 points in each case:

| Calibration | N (Lean-certified) | Lean-certified bound | **measured** iteration error (double precision) | **measured** `cv2.undistortPoints` error |
|---|---|---|---|---|
| TUM fr1 | 17 | < 0.001 px | **1.4×10⁻¹⁰ px** | 3.7×10⁻³ px |
| TUM fr2 | 26 | < 0.001 px | **5.8×10⁻¹³ px** | 2.0×10⁻² px |
| Azure Kinect DK | 59 | < 0.001 px | **1.4×10⁻¹³ px** | 4.5×10⁻⁸ px |

**Reading this honestly, per task instruction not to treat numerics as a formal
guarantee:**

- The **measured** double-precision iteration error is 7–10 orders of magnitude smaller
  than the **certified** bound. This is evidence the certified bound is sound (no
  observed violation) and very conservative — **not** a claim that the certified bound is
  tight, and not a substitute for it: the certified bound is the only one of these three
  numbers with a Lean proof behind it.
- `cv2.undistortPoints` — OpenCV's own production numerical solver, a genuinely
  independent implementation — is **less accurate** than our proof-mirroring iteration at
  the Lean-certified `N`, for both TUM cameras (by 7–10 orders of magnitude), and
  noticeably better for Kinect. No explanation for this asymmetry is offered here (likely
  related to OpenCV's own default iteration count/stopping criteria, which were not
  inspected) — it is reported as a measured fact, not diagnosed.
- None of this is a claim that *this project's* floating-point evaluation of the
  recurrence is correct to any particular tolerance in general — only that it was,
  empirically, at these 2000×3 sampled points.

---

## 7. Audit: domain invariance, denominator safety, contraction, hidden assumptions (task item 5)

### 7.1 Domain invariance

The iteration `(inverseStepRTight ... y)^[n] y` staying inside the certified disk `{z |
‖z‖ ≤ R}` at every step is **not a new concern this file introduces** — it is exactly
what `hMapsTo : Set.MapsTo (inverseStepRTight ... y) s s` (reused unchanged from
`RDist_exists_unique_preimage_tight_pos`/`_neg`) already establishes, and Mathlib's
`ContractingWith.exists_fixedPoint'` internally restricts its iteration to `s` via
`hMapsTo.restrict` before proving the rate bound — so the rate bound this file extracts
is *already* a statement about an iteration that never leaves the certified disk. No
separate domain-invariance argument was added or needed.

### 7.2 Denominator safety and contraction hypotheses

`hsafe`/`hcontract` (Kinect) and `hcontract` (fr1/fr2) are the **identical** hypotheses
`RDist_exists_unique_preimage_tight_pos`/`_neg` already require — this file adds no new
side conditions beyond them. The three concrete instantiations (§5) reuse the exact same
discriminant/monotonicity/contraction facts (`fr1_disc_h`, `fr1_contraction_improved`,
`kinect_hsafe`, `kinect_hcontract`, etc.) already proved and `#print axioms`-verified in
`Pipeline/RealCalibrationExamplesImproved.lean`/`Pipeline/RealCalibrationKinectImproved.lean`
— none were re-derived or modified.

### 7.3 Non-degeneracy checks preserved

No new example points were introduced that could reintroduce the `k1=k4` identity-collapse
class of defect (`audit/BOUNDED_DOMAIN_INVERTIBILITY.md` §6): §5's theorems are universally
quantified over `y` (any point satisfying the buffer hypothesis), not instantiated at a
single possibly-degenerate point, and reuse the SAME `θ_fr1`/`θ_fr2`/`θ_kinect`
coefficient sets whose non-identity properties (`fr1_not_identity_improved`,
`fr2_not_identity_improved`, `kinect_not_identity`) were already established and are
untouched by this pass.

### 7.4 A genuine finding: certified coverage trades off against convergence speed

The self-audit (as required by task item 5) surfaced a real, non-obvious fact, not
assumed going in: §4's capstone row (TUM fr2 at `R=79/100`, the radius proved in
`Pipeline/FullImageInjectivity.lean` to certify the **entire** image rectangle) needs
**204** iterations for the same 0.001 px guarantee that the smaller `R=3/4` disk achieves
in **26** — because `K=LPertTightPos` rises from `0.643` to `0.938` as `R` grows toward
the validity boundary, and convergence rate is governed by `K^N`, which is extremely
sensitive to `K` approaching `1`. **This is a genuine tension, not a defect**: maximizing
certified *coverage* (bigger `R`) and maximizing certified *convergence speed* (smaller
`R`, smaller `K`) pull in opposite directions, and no single radius is best for both
purposes. §5 deliberately uses the smaller, faster-converging `R=3/4` for fr2 rather than
the full-image `R=79/100` — a choice made explicit here, not buried.

### 7.5 Hidden-assumption check

- **No new axioms.** `ennreal_rate_bound_toReal` is pure algebra (`ENNReal.ofReal`
  manipulation) with no hypothesis beyond `K<1`, `A,K≥0` — all three already required by
  the surrounding proofs.
- **The ENNReal→ℝ conversion does not silently discard information**: every step
  (`ENNReal.ofReal_mul`, `ENNReal.ofReal_div_of_pos`, `ENNReal.ofReal_pow`,
  `ENNReal.ofReal_sub`, `ENNReal.ofReal_le_ofReal_iff`) is an iff/exact-equality lemma
  from Mathlib, not an inequality relaxation beyond what was already present in the
  original ENNReal statement.
- **The starting point `z_0 = y` is not hidden** — it is the explicit, named argument the
  theorem is stated for, matching the convention used throughout this project's own
  numerical cross-checks (not a convenience chosen to make the bound look better; a worse
  starting guess would simply enter via a different, equally provable, instance of the
  same general theorem).

---

## 8. Build and axiom summary

```
$ lake build
Build completed successfully (8408 jobs).
```

`#print axioms` on `RDist_iteration_error_bound_tight_pos`, `RDist_iteration_error_bound_tight_neg`,
`ennreal_rate_bound_toReal`, `fr1_pixel_error_bound_N17`, `fr2_pixel_error_bound_N26`,
`kinect_pixel_error_bound_N59`: all depend only on `propext, Classical.choice,
Quot.sound`. Forbidden-construct scan (`sorry`/`admit`/custom `axiom`/`native_decide`/
`unsafe`/`partial`, word-boundary regex) across both new files: zero matches.

---

## 9. Remaining limitations (reported, not resolved)

- **Floating-point/production correctness is not claimed.** §2's disclaimer is binding;
  §6's numerical cross-check is evidence, not a proof, of double-precision behavior.
- **The bounds are conservative, not tight** (§6: 7–10 orders of magnitude of slack
  observed at the certified `N`) — a sharper (non-conservative) Lipschitz/boundedness
  analysis would likely allow much smaller `N` for the same guarantee, but was not
  attempted here; this document uses the EXISTING `MPertTightPos`/`LPertTightPos` bounds
  from prior passes unchanged, as instructed.
- **SQ-CV-07 and native OpenLensIO D→U interoperability** — untouched, as in every prior
  document in this series.
- **Only the trivial-denominator (fr1/fr2) and one rational-denominator (Kinect) case are
  Lean-instantiated at a concrete `N`.** The general theorems (§3.2) apply to any
  calibration satisfying the same hypotheses, but no further camera was instantiated.
- **The full-image-coverage fr2 radius (`R=79/100`) was not Lean-verified at its own
  (much larger, N=204) iteration count** — only computed numerically (§4) — since §7.4's
  finding already makes the qualitative point (coverage/speed tradeoff) without needing a
  second, much more expensive `norm_num` computation at N=204.
