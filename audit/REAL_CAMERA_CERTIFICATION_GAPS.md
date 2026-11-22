# Closing the Real-Camera Certification Gaps

Closes the two scope gaps `audit/IMPROVED_REAL_CALIBRATION_BOUNDS.md` left open: (1) Azure
Kinect DK's `RDist`→`CVmap`/`SensorPoint` bridge was blocked on an unproved *global*
denominator-nonvanishing fact; (2) TUM fr2's "full-image injectivity" claim rested on a
Python corner-radius calculation, not a Lean theorem. **Both are now closed as genuine,
kernel-checked Lean theorems**, with the injectivity/existence distinction the task asked
for made explicit and enforced by using two separately-named theorems rather than one
conflated claim.

**Keeps explicitly unresolved, unchanged from both prior documents:** SQ-CV-07, native
OpenLensIO D→U interoperability, and floating-point/production correctness.

---

## 1. Executive summary

| Task item | Result |
|---|---|
| 1. Azure Kinect DK global denominator positivity + `RDist`→`CVmap` bridge | **Done** — `kinect_den_global_lower`/`kinect_hden_global` (`Pipeline/KinectGlobalDenominator.lean`) prove `1+k4u+k5u²+k6u³ > 0` for **all** `u≥0` (not just the certified disk) using the real Kinect coefficients; `kinect_CVmap_invertible` then instantiates `CVmap_inverse_invOn_tight_neg` with this proved fact, completing the bridge `audit/IMPROVED_REAL_CALIBRATION_BOUNDS.md` §6 left as a free hypothesis. |
| 2. TUM fr2 full-image injectivity as a complete Lean theorem | **Done** — `fr2_image_rect_subset_cert_disk` (`Pipeline/FullImageInjectivity.lean`) proves, from fr2's actual `fx,fy,cx,cy` and actual `640×480` dimensions, that every pixel in the rectangle maps into the certified disk; `fr2_full_image_injective` combines this with a new injectivity-only corollary to conclude `CVmap` is injective over the **entire** image rectangle — no numerical corner check substitutes for any step. |
| 3. Distinguish injectivity from existence; certify lower bounds where feasible | **Done** — `fr2_full_image_injective` (100%, Lean-proved, injectivity only) is kept **separate** from `fr2_CVmap_invertible_capstone` (existence, restricted to the smaller `MPert`-buffered region, ≈98.5% by the Python-only area estimate carried over unchanged from `IMPROVED_REAL_CALIBRATION_BOUNDS.md`). No measure-theoretic Lean statement of the *existence* region's area fraction was attempted — see §4's honest limitation. |
| 4. Reuse, preserve non-identity, no new axioms/weakened conclusions | **Done** — see §5; every new file imports and reuses prior theorems (`cubic_tight_neg`, `Pert_lipschitz_tight_pos`, `CVmap_eq_RDist`, `CVmap_inverse_invOn_tight_neg`, `fr2_disc_h_capstone` etc.) rather than re-deriving them; `kinect_not_identity`/`fr2_not_identity_improved` from prior files are untouched and still apply unchanged to the (same) certified-disk examples. |
| 5. Full build, axiom audit | **Done** — §6: `lake build` 8406 jobs, exit 0 (4 new files); every new top-level theorem axiom-clean. |

---

## 2. Azure Kinect DK: global denominator positivity (task item 1)

### 2.1 The obstacle, precisely

`audit/IMPROVED_REAL_CALIBRATION_BOUNDS.md` §6 identified that `CVmap`'s `hden`
hypothesis is universally quantified over **all** real `x', y'` — not restricted to any
disk — and that the `cubic_tight_neg`/`quad_mono_nonpos` monotonicity machinery built for
the bounded-disk Kinect example only certifies behaviour on a single interval `[0,U]`,
which cannot cover a function that dips to an interior minimum and then rises without
bound.

### 2.2 The fix: an 8-region, gap-free cover of `[0,∞)`

Two new general lemmas (`Pipeline/SignedCubicBoundsGlobal.lean`), reusing
`cubic_diff_eq_mul` and the quotient-style divided-difference technique throughout
`Pipeline/SignedCubicBounds.lean`:

- **`cubic_bounded_piece_lower(a,b,c,L,U)`**: `f(u) ≥ f(L)+(U-L)·f'(L)` for `u∈[L,U]`,
  given `b+3cL≥0` (the SAME vertex condition as `cubic_tight_neg`, generalized to an
  arbitrary left endpoint `L`, not just `L=0`) and `f'(L)≤0`.
- **`cubic_tail_lower(a,b,c,L)`**: `f(u) ≥ f(L)` for **all** `u≥L` (no upper bound), given
  the same vertex condition and `f'(L)≥0`.

The key to covering `[0,∞)` with **no gap**: the boundary between "`cubic_tight_neg`
applies" (needs `b+3cU≤0`) and "`cubic_bounded_piece_lower` applies" (needs `b+3cL≥0`) is
the **exact rational**

```
Lstar := -k5/(3·k6) = 2138909339904785/4838702917098999
```

(a ratio of the two given rational coefficients — **not** an irrational approximation;
only the cubic's *roots* would need `Real.sqrt`, and this is its derivative's *vertex*,
which needs none). `norm_num` confirms `k5+3·k6·Lstar = 0` exactly, so **both** conditions
hold (as equalities) at precisely this point — the two argument types meet with zero gap,
not an approximation that leaves a sliver uncovered.

`Pipeline/KinectGlobalDenominator.lean`'s `kinect_den_global_lower` chains:

| Region | Argument | Lean |
|---|---|---|
| `[0, Lstar]` | `cubic_tight_neg` (existing, unmodified) | 1 case |
| `[Lstar, 1]`, split at `1/2, 6/10, 7/10, 8/10, 9/10` | `cubic_bounded_piece_lower` ×6 | 6 cases |
| `[1, ∞)` | `cubic_tail_lower` (unbounded, `f'(1)=0.2947>0` confirmed) | 1 case |

Each case's hypotheses (`b+3cL≥0`/`≤0`, `f'(L)≤0`/`≥0`) are discharged by `norm_num` on
the exact rational coefficients — no numerical tolerance, no floating point. The worst
margin across all 8 regions is `Dden ≥ 0.184` (comfortably `>0`; the true global minimum,
found only numerically, is `≈0.1995` — the Lean bound is conservative but not by much).

### 2.3 The completed bridge

`kinect_hden_global : ∀ x' y' : ℝ, 1+k4(x'²+y'²)+k5(...)²+k6(...)³ ≠ 0` follows directly
(`u := x'²+y'² ≥ 0` always). `kinect_CVmap_invertible` then instantiates
`CVmap_inverse_invOn_tight_neg` (reused, unmodified) with this **proved** `hden`, giving:

```lean
theorem kinect_CVmap_invertible :
    Set.InvOn
      (toComplexEquiv.symm ∘ RDistInvTightNeg ... ∘ toComplexEquiv)
      (CVmap k1 k2 k3 k4 k5 k6 p1 p2 kinect_hden_global)
      (toComplexEquiv.symm '' {z | ‖z‖ ≤ 2/5 ∧ ‖RDist θ_kinect z‖ + MPertTightNeg ... ≤ 2/5})
      (toComplexEquiv.symm '' {y | ‖y‖ + MPertTightNeg ... ≤ 2/5})
```

— a genuine `SensorPoint`-level existence/uniqueness theorem for Azure Kinect DK's actual
rational denominator, something no prior document in this repository had.

**What this does NOT change:** the certified radius is still `R=2/5` (unchanged from
`Pipeline/RealCalibrationKinectImproved.lean`) and the numeric image-coverage percentage
is still the `~13.3%` figure from `IMPROVED_REAL_CALIBRATION_BOUNDS.md` §4 — this pass
closes a **qualitative** gap (the bridge existing at all), not a coverage-size
improvement. Re-optimizing `R` for Kinect using the global result is not attempted here.

---

## 3. TUM fr2: full-image injectivity as a complete theorem (task item 2)

### 3.1 Pixel-to-normalised-coordinate formalization

The standard pinhole relation (already used informally throughout this repository's `F`,
`ΔPx`, `ΔPy` pixel-level theorems) is made explicit: pixel `(px,py)` corresponds to
normalised sensor point `⟨(px-cx)/fx, (py-cy)/fy⟩`. `fr2_image_rect_subset_cert_disk`
proves, from fr2's own `fx=520.908620, fy=521.007327, cx=325.141442, cy=249.701764` and
image dimensions `640×480` (all as exact rationals, same published values used
throughout this repository's other fr2 theorems):

```lean
theorem fr2_image_rect_subset_cert_disk (px py : ℝ)
    (hpx0 : 0 ≤ px) (hpxw : px ≤ 640) (hpy0 : 0 ≤ py) (hpyh : py ≤ 480) :
    ((px - 325141442/1000000) / (520908620/1000000)) ^ 2
      + ((py - 249701764/1000000) / (521007327/1000000)) ^ 2 ≤ ((79:ℝ)/100) ^ 2
```

**Proof method**: a new, reusable, two-line-proof lemma `sq_le_max_of_mem_Icc(A,B,y)`
(`y∈[A,B] ⟹ y² ≤ max(A²,B²)`, by a sign case split — no calculus) applied independently
to the `px` and `py` coordinates, then combined. The resulting per-axis bound is attained
exactly at the corner `(px,py)=(0,0)` — confirmed as the same worst corner
`IMPROVED_REAL_CALIBRATION_BOUNDS.md`'s Python computation found, but now this is a
**consequence of a Lean proof**, not an input assumed from it.

### 3.2 Full-image injectivity

`fr2_full_image_injective` composes this containment fact with a **new**
injectivity-only corollary (`CVmap_injective_on_disk_tight_pos`,
`Pipeline/TightBoundsInjectivity.lean` — see §3.3) to conclude:

```lean
theorem fr2_full_image_injective :
    Set.InjOn (CVmap k1 k2 k3 0 0 0 p1 p2 hden_fr2_improved)
      (toComplexEquiv.symm ''
        ((fun (p : ℝ × ℝ) => pixel-to-sensor-point p)
          '' {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 640 ∧ 0 ≤ p.2 ∧ p.2 ≤ 480}))
```

— `CVmap` does not identify any two distinct pixels anywhere in the **entire** 640×480
image rectangle. This is a complete, kernel-checked theorem: the domain set is literally
the image of the full pixel rectangle (not an abstract disk assumed to contain it), and
`#print axioms` confirms no axioms beyond the standard three.

### 3.3 Why a NEW injectivity-only lemma was needed (not reused as-is)

`CVmap_inverse_invOn_tight`/`fr2_CVmap_invertible_capstone` (the existing existence
theorem) is stated over the **smaller**, `MPert`-buffered domain
`{z | ‖z‖≤R ∧ ‖RDist z‖+MPert≤R}` — `Set.InvOn`'s `LeftInvOn` component would only give
injectivity on *that* restricted set, not the full disk `{‖z‖≤R}` the image rectangle
actually needs (recall `R=79/100` slightly exceeds the image's own corner radius, so the
relevant containment is w.r.t. the **full** disk, not the buffer-shrunk one).
`RDist_injective_on_disk_tight_pos`/`CVmap_injective_on_disk_tight_pos`
(`Pipeline/TightBoundsInjectivity.lean`) close this by mirroring
`RationalDistortionInjectivity.lean`'s original `RDist_eq_implies_eq`/
`RDist_injective_on_disk` pattern with `Pert_lipschitz_tight_pos` (reused, unmodified)
substituted in — establishing injectivity needs **only** the Lipschitz contraction
(`LPertTightPos < 1`), not the existence-side buffer condition. This is precisely the
distinction task item 3 asked to be made explicit, and it surfaced a genuine missing
piece of infrastructure (not merely a documentation gap) — the theorem did not exist
before this pass.

### 3.4 What is NOT claimed

`fr2_full_image_injective` is an injectivity statement only. It does **not** assert that
every pixel's distorted image has a computable preimage that itself lies back in the
image rectangle (or even in the certified disk) — that is exactly what
`fr2_CVmap_invertible_capstone`'s smaller buffered domain addresses, and its ≈98.5% area
estimate (not a Lean theorem) is carried over unchanged. Injective-but-not-necessarily-
surjective-onto-a-useful-region is a real, meaningful distinction, not a formality: a map
can be injective everywhere while still having preimages outside any particular target
region for some of its image points near the domain's edge.

---

## 4. Remaining limitations (reported, not resolved)

- **SQ-CV-07, OpenLensIO D→U interoperability, floating-point/production correctness**
  — untouched, as in both prior documents.
- **TUM fr1 and Azure Kinect DK do not have an image-rectangle-containment Lean theorem**
  — only fr2 (task item 2's explicit minimum target) was formalized this way. fr1's own
  corner radius (`≈0.794`) is known (from `REAL_CALIBRATION_VALIDATION.md`) to slightly
  **exceed** its tight `R*≈0.766`, so fr1 could not achieve full-image injectivity even
  with this formalization effort — a `fr1_image_rect_subset_cert_disk`-style theorem
  would need to report a genuine **partial** (not full) containment, which was not
  attempted in this pass.
- **No measure-theoretic Lean statement of the EXISTENCE region's area fraction.** The
  ≈98.5%/≈13.3% "area %" figures throughout both audit documents remain Python-computed
  rectangle-disk-intersection estimates, not Lean `MeasureTheory.volume` computations.
  Formalizing this would require Mathlib's integration/measure machinery for a disk-
  rectangle intersection — a substantially different (and substantial) undertaking not
  in scope here.
- **Kinect's certified radius (`R=2/5`) was not re-optimized** using the newly-available
  global denominator fact; the global result closes the `CVmap` bridge but does not by
  itself enlarge the certified disk or its ≈13.3% image-coverage figure.
- **The 8-region Kinect cover's bounds are not claimed tight.** The true global
  denominator minimum (`≈0.1995`, found only numerically) is comfortably above the
  worst proved bound (`0.184`), but the gap between them reflects the piecewise linear
  lower bound's own conservativeness, not an attempt at the sharpest possible argument.

---

## 5. Reuse and non-degeneracy discipline (task item 4)

No existing theorem was modified or weakened; every new file is purely additive:

| New file | Imports (reuses) |
|---|---|
| `Pipeline/SignedCubicBoundsGlobal.lean` | `Pipeline.SignedCubicBounds` (`cubic_diff_eq_mul`) |
| `Pipeline/KinectGlobalDenominator.lean` | `Pipeline.SignedCubicBoundsGlobal`, `Pipeline.RealCalibrationKinectImproved` (all `kinect_*` disk-level hypotheses, `CVmap_inverse_invOn_tight_neg`) |
| `Pipeline/TightBoundsInjectivity.lean` | `Pipeline.TightBoundsNoDenominator` (`Pert_lipschitz_tight_pos`, `RDist_eq_add_Pert`, `CVmap_eq_RDist`, `toComplexEquiv`) |
| `Pipeline/FullImageInjectivity.lean` | `Pipeline.TightBoundsInjectivity`, `Pipeline.RealCalibrationExamplesImproved` (`fr2_disc_h_capstone` etc., `hden_fr2_improved`) |

Non-identity checks from prior passes (`kinect_not_identity`, `fr2_not_identity_improved`)
are untouched and still apply to the same concrete points on the same certified disks —
nothing in this pass alters the calibration data, the Brown-Conrady model definitions, or
any previously-stated theorem conclusion.

---

## 6. Build and axiom summary

```
$ lake build
Build completed successfully (8406 jobs).
```

`#print axioms` on every new top-level theorem (`kinect_den_global_lower`,
`kinect_hden_global`, `kinect_CVmap_invertible`, `sq_le_max_of_mem_Icc`,
`fr2_image_rect_subset_cert_disk`, `fr2_full_image_injective`,
`RDist_injective_on_disk_tight_pos`, `CVmap_injective_on_disk_tight_pos`): all depend
only on `propext, Classical.choice, Quot.sound`. Forbidden-construct scan
(`sorry`/`admit`/custom `axiom`/`native_decide`/`unsafe`/`partial`, word-boundary regex)
across all four new files: zero genuine matches (two doc-comment mentions of the word
"sorry" inside sentences stating its absence).
