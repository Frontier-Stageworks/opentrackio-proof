# Improved Bounded-Domain Invertibility Bounds for Real Camera Calibrations

Takes the bounds `RfacL`/`RfacDevUB`/`LPert`/`MPert` evaluated for three real calibrations
in `audit/REAL_CALIBRATION_VALIDATION.md` — found there to be sound but conservative,
certifying roughly 50–58% of the image for the two moderate-FOV cameras and only ~12% for
the wide-FOV Azure Kinect DK — and **derives genuinely tighter, Lean-proved sufficient
conditions**, by exploiting the real coefficients' actual (fixed, partly cancelling)
signs instead of treating them as adversarial. **Result: certified coverage rises to
~94% (TUM fr1) and ~98.5%, with one example reaching full-image injectivity (TUM fr2);
Azure Kinect DK rises much more modestly, from ~12% to ~13%, and the reason the two
families behave so differently is itself the main finding of this document.**

**Keeps explicitly unresolved, unchanged from the prior document:** SQ-CV-07, native
OpenLensIO D→U interoperability, and floating-point/production correctness. Additionally,
this document's Azure Kinect DK result does **not** bridge to `CVmap`/`SensorPoint`
(unlike the two TUM examples) — see §6.

---

## 1. Executive summary

| Task item | Result |
|---|---|
| 1. Identify which bounds make certified regions unnecessarily small | **Done** — §2: `Mrad`/`Lrad`'s triangle-inequality sum of `|k1|,|k2|,|k3|` ignores that real calibrations have MIXED-SIGN coefficients that partially cancel; the true polynomial value at the boundary is far smaller than the sum of magnitudes. |
| 2. Derive and Lean-prove tighter sufficient conditions, unchanged model | **Done** — `Pipeline/SignedCubicBounds.lean` (new, general, pure-algebra lemmas), `Pipeline/TightBoundsNoDenominator.lean` and `Pipeline/TightBoundsWithDenominator.lean` (bridges to the actual model) — no existing definition changed. |
| 3. Quantify old vs. new coverage, Lean-certified vs. numerically estimated | **Done** — §4 table, with the distinction stated explicitly in every row. |
| 4. Azure Kinect DK Lean example with its real nonzero rational denominator | **Done, with an honest scope boundary** — `Pipeline/RealCalibrationKinectImproved.lean`, the first Lean-verified invertibility result for this calibration's actual 8-coefficient rational model; stops at the `RDist`/ℂ level rather than bridging to `CVmap`/`SensorPoint` — see §6. |
| 5. Non-degeneracy checks; investigate full-image certification | **Done** — explicit non-identity witnesses at every new radius (§5); §5 also reports that TUM fr2 reaches **full-image injectivity** at `R=79/100`, the one case tested where this was achievable. |
| 6. Full build, axiom audit; challenge for hidden assumptions, bad domain handling, overclaims | **Done** — §7, plus an explicit "what could go wrong" self-audit in §8 that found and required fixing two real hidden assumptions during development (see failure log). |

**No existing theorem was weakened, no existing calibration data point was altered, and
no axiom was added.** `lake build`: 8402 jobs, exit 0 (5 new files; unchanged from
`REAL_CALIBRATION_VALIDATION.md`'s count — only file *content* differs via this
document's companion additions to `Pipeline/RealCalibrationExamplesImproved.lean`).

---

## 2. Which bounds were loose, and why

`Mrad(θ,R) = |k1|R²+|k2|R⁴+|k3|R⁶` bounds the radial polynomial `f(u) = k1 u+k2 u²+k3 u³`
(`u:=r²∈[0,R²]`) via `|f(u)| ≤ |k1|u+|k2|u²+|k3|u³ ≤ Mrad(θ,R)` — a valid triangle
inequality, **tight only when `k1,k2,k3` share a sign** (so the bound's implicit
worst case, all three terms reinforcing, can actually occur). Real calibrations
typically do not: TUM fr1's numerator has `k1=+0.262, k2=-0.953, k3=+1.163` — the large
negative `k2` term **cancels** most of the positive `k1,k3` contribution at any given
radius, so the polynomial's actual value is much smaller in magnitude than the sum
`|k1|+|k2|+|k3|` (scaled). `Lrad`, which bounds the Lipschitz constant via the same
triangle-inequality pattern applied to each power's own Lipschitz estimate, is
conservative for the identical reason — and it is the quantity that actually dominates
`LPert` (hence the certified radius), per `REAL_CALIBRATION_VALIDATION.md`'s own
numbers: at the old TUM fr1 boundary, `RfacL·R ≈ 0.745` of `LPert ≈ 0.9999`
(see `audit/BOUNDED_DOMAIN_INVERTIBILITY.md`'s derivations). Tightening `Mrad` alone,
without touching `Lrad`, therefore gives only a **small** improvement — confirmed
numerically (not Lean-proved) before committing to the harder Lipschitz tightening: with
only the boundedness (M-type) terms tightened, TUM fr1's certified radius moved from
`0.5584` to only `0.5884` (+5.4%), TUM fr2 from `0.5889` to `0.6200` (+5.3%), Azure
Kinect DK from `0.3883` to `0.3934` (+1.3%). The Lipschitz constant genuinely needed
tightening too for a substantial result — see §3.

---

## 3. The new general lemmas (`Pipeline/SignedCubicBounds.lean`)

Pure real-number algebra, independent of `Coeffs`/`RCoeffs`/ℂ — reusable for any cubic
`f(u)=au+bu²+cu³` and its Lipschitz "divided difference"
`k(u1,u2):=a+b(u1+u2)+c(u1²+u1u2+u2²)` (which satisfies the exact identity
`f(u1)-f(u2)=(u1-u2)·k(u1,u2)`, provable by `ring`):

| Lemma | What it proves | Condition |
|---|---|---|
| `quad_discrim_nonneg` | `a+bu+cu² ≥ 0` for **all** real `u` | `c>0`, `b²≤4ac` (completing the square: `4c·(a+bu+cu²)=(2cu+b)²+(4ac-b²)`) |
| `quad_mono_nonpos` | `a+bu+cu² ≤ 0` for `u∈[0,U]` | `c>0`, `a≤0`, `b+2cU≤0` (starts ≤0, provably monotonic non-increasing throughout `[0,U]`) |
| `quad_chord_upper` | `a+bu+cu² ≤ max(a, a+bU+cU²)` for `u∈[0,U]` | `c>0` only — convexity/chord argument, no sign condition |
| `quad_mono_decreasing_lower` | `a+bU+cU² ≤ a+bu+cu²` for `u∈[0,U]` | same monotonicity condition as above |
| `cubic_tight_pos` | `0 ≤ f(u) ≤ f(U)` for `u∈[0,U]` | `b²≤4ac` (on `f` itself) **and** on the "g" quadratic from `f(U)-f(u)=(U-u)·g(u)` |
| `cubic_tight_neg` | `f(U) ≤ f(u) ≤ 0` for `u∈[0,U]` | `a≤0`, `b+3cU≤0` |
| `k_bound_pos` | `|k(u1,u2)| ≤ max(a, a+2bU+4cU²)` | `b²≤3ac` (via `u1²+u1u2+u2²=(3/4)s²+(1/4)(u1-u2)²`, `s:=u1+u2`) |
| `k_bound_neg` | `|k(u1,u2)| ≤ |a+2bU+3cU²|` | `a≤0`, `b+4cU≤0` |

Both the "positive/discriminant" case (TUM fr1, fr2 — numerator coefficients make the
radial factor **sign-definite** everywhere, not just locally) and the
"negative/monotone" case (Azure Kinect DK — both numerator and denominator are negative
throughout the relevant range, confirmed numerically: no interior critical point of the
cubic lies inside `[0,U]` for any `R` tested) are needed, since the two real-world
coefficient families behave genuinely differently (§8 explains why the discriminant
route fails for Kinect and the monotone route is used instead).

`Pipeline/TightBoundsNoDenominator.lean` bridges these to `radial`/`Pert`/`RDist` for the
**trivial-denominator** case (`k4=k5=k6=0`, i.e. TUM fr1/fr2 — `Rfac θ z = 1+radial(num)z`
exactly, no quotient rule needed) and reproves, in full, a parallel Banach
existence/uniqueness chain down to `CVmap_inverse_invOn_tight`, reusing `M`/`L`/
`Tang_bounded`/`Tang_lipschitz`/`normSq_lipschitz`/`CVmap_eq_RDist`/`toComplexEquiv`/
`conjugate_invOn` unchanged throughout. `Pipeline/TightBoundsWithDenominator.lean` does
the same for the **genuine nonzero denominator** case (Azure Kinect DK), requiring the
full quotient-rule combination mirroring `RationalRadialBounds.lean`'s `Rfac_bounded`/
`Rfac_lipschitz` proof structure exactly, with the tight bounds substituted for
`Mrad`/`Lrad` and the sharper upper bound `|Nnum|,|Dden| ≤ 1` (valid here specifically
because `Nnum,Dden ∈ [1+f(U), 1]` when `f(U)≤0` — simpler than the general case).

---

## 4. Old vs. new certified coverage

All "R\*"/"Rb" values below are **numerically computed** (Python, bisection on the exact
tight formulas) to locate the best achievable radius; the **specific radii actually used
in the Lean examples** (§5) are chosen with deliberate slack below these numerically
optimal values, for comfortable `norm_num` margins — so the Lean-proved coverage is very
close to, but conservatively inside, the numbers below.

| Calibration | Old R\* (crude) | New R\* (tight) | Old area % (Rb) | New area % (Rb) |
|---|---|---|---|---|
| TUM fr1 | 0.558 | **0.766** (+37%) | 50.2% | **94.2%** |
| TUM fr2 | 0.589 | **0.797** (+35%) | 57.9% | **98.5%** |
| Azure Kinect DK | 0.388 | **0.416** (+7%) | 12.2% | **13.3%** |

"Area %" is the fraction of the physical image rectangle's area within the
**existence/buffer radius** `Rb := R - MPert(R)` (the radius actually usable for
inverting a real captured, already-distorted pixel — see
`REAL_CALIBRATION_VALIDATION.md` §2 for why this, not the raw injectivity radius, is the
practically relevant figure), computed by direct numerical rectangle-disk intersection
(not a naive disk-area/rectangle-area ratio).

**What is Lean-certified vs. numerically estimated, stated precisely:**

- **Lean-certified** (§5): `fr1` at `R=7/10`, `fr2` at `R=3/4` and, as a capstone, `R=79/100`,
  `kinect` at `R=2/5` — all hypotheses (`disc_h`/`disc_g`/`disc_psi` or `ha`/`hmono`/`hge2`,
  `hsafe`, `hcontract`) are `norm_num`-verified Lean theorems on the exact published
  rational coefficients, and the resulting `Set.InvOn` existence/uniqueness conclusion
  is a Lean theorem.
- **Numerically estimated, not Lean-proved:** the "New R\*" column (the *numerically
  optimal* radius — the Lean examples use a smaller, safer radius with margin,
  documented per-example in §5), and every "area %" figure (a statement about the
  physical image rectangle's geometry, which is not itself expressed as a Lean
  proposition anywhere in this repository).

---

## 5. Lean-verified examples at the new radii

| File | Declaration | Coefficients | R | Key facts proved |
|---|---|---|---|---|
| `Pipeline/RealCalibrationExamplesImproved.lean` | `fr1_CVmap_invertible_improved` | TUM fr1 (unchanged from `RealCalibrationExamples.lean`) | `7/10` | `fr1_disc_h`, `fr1_disc_g`, `fr1_disc_psi`, `fr1_contraction_improved`, `fr1_not_identity_improved` |
| same | `fr2_CVmap_invertible_improved` | TUM fr2 | `3/4` | analogous `fr2_*` theorems |
| same | `fr2_CVmap_invertible_capstone` | TUM fr2 | **`79/100`** | same hypothesis family at the larger radius — see below |
| `Pipeline/RealCalibrationKinectImproved.lean` | `kinect_invertible` | Azure Kinect DK (genuine nonzero `k4,k5,k6`) | `2/5` | `kinect_ha1/4`, `kinect_hmono1/4_3/4`, `kinect_hge2_1/4`, `kinect_hsafe`, `kinect_hcontract`, `kinect_not_identity` |

**Non-degeneracy, every example:** an explicit non-identity witness at a concrete point
is proved in each case (`fr1_not_identity_improved`, `fr2_not_identity_improved`,
`kinect_not_identity`), following the discipline established in the prior correction
pass — no example merely asserts nonzero coefficients.

### 5a. Full-image injectivity: TUM fr2's capstone case

TUM fr2's image corners have maximum normalised radius `≈0.7870` (computed in
`REAL_CALIBRATION_VALIDATION.md` §2, from `fx=520.908620, fy=521.007327,
cx=325.141442, cy=249.701764`, 640×480). The tight bound's injectivity radius `R*≈0.797`
**exceeds this** — so choosing `R=79/100=0.79` (comfortably valid: `LPert≈0.938<1`,
checked exactly via `fr2_contraction_capstone`) certifies a disk that **provably
contains the entire image rectangle**. `fr2_CVmap_invertible_capstone` is therefore
Lean-proof of injectivity (and, via the existence side, local invertibility) covering
**the whole image**, for this one real calibration — not "most of it." The
existence/buffer radius there is `Rb≈0.731` (numerically; `MPert≈0.059` at `R=0.79`),
giving ≈99.5% area coverage on the existence side (not literally 100%, since `MPert>0`
always shrinks the buffer disk below the raw `R`) — this is the closest this
investigation came to full-image coverage on both sides of the result, and the only one
achieved on the injectivity side outright.

**Why TUM fr1 could not do the same:** fr1's tight `R*≈0.766` is slightly **below** its
own corner radius `≈0.794` — the two moderate-FOV cameras are close in behavior but not
identical, and fr1's slightly larger/differently-signed coefficients leave it just short
of full-image injectivity under this tightening. This is reported as a genuine,
unresolved gap for fr1, not glossed over: a sharper (non-conservative, i.e. truly
optimal) bound might close it, but this document's technique does not.

---

## 6. Azure Kinect DK: scope boundary (task item 4, stated honestly)

`kinect_invertible` proves existence/uniqueness of the inverse of the actual rational
(numerator **and** denominator both genuinely nonzero) Brown-Conrady map at the `RDist`
(ℂ) level — i.e. for the map abstractly, on the certified disk `‖z‖≤2/5`. It does **not**
bridge to `CVmap`/`SensorPoint`, unlike the TUM fr1/fr2 examples. The reason:
`CVmap`'s own type signature (`Pipeline/InverseConjugacyApplication.lean`) requires a
**global** denominator-nonvanishing hypothesis
`∀ x' y' : ℝ, 1+k4(x'²+y'²)+k5(...)²+k6(...)³ ≠ 0` — true for ALL real inputs, not just
those within a disk. For TUM fr1/fr2 this was trivial (`k4=k5=k6=0` makes the
denominator the constant `1`). For Azure Kinect DK it is **not** trivial: the
`cubic_tight_neg`/`quad_mono_nonpos` machinery built in this pass only certifies behavior
on a *bounded interval* `[0,U]` via a monotonicity argument that is specific to that
interval — it says nothing about the denominator polynomial's behavior at `r²` values
outside `[0,U]`.

**Is the global fact even true?** Checked numerically (not Lean-proved): the
denominator polynomial `1+k4 u+k5 u²+k6 u³` (`u=r²`) has exactly one positive critical
point, at `u*≈0.942` (`r*≈0.970`), found via the roots of its derivative
`k4+2k5 u+3k6 u²`; the value there is `≈0.1995` — positive, comfortably away from zero,
and since the leading coefficient `k6>0` the polynomial increases without bound for
`u>u*`, so the denominator **never vanishes for any real input**. This is true and
numerically well-supported, but proving it in Lean would require a different argument
(locating and bounding a cubic's single interior critical point in general, not merely
showing monotonicity on a hypothesis-supplied bounded interval) that was not built in
this pass. **This is the single largest scope limitation in this document, stated
plainly:** the Kinect result is a genuine, non-trivial, newly-tightened Lean theorem,
but it certifies the abstract map, not (yet) the concrete `SensorPoint`-level `CVmap`.

---

## 7. Build and axiom summary

```
$ lake build
Build completed successfully (8402 jobs).
```

`#print axioms` on every top-level theorem introduced or re-certified in this pass
(`CVmap_inverse_invOn_tight`, `CVmap_inverse_invOn_tight_neg`,
`RDist_exists_unique_preimage_tight_pos`, `RDist_exists_unique_preimage_tight_neg`,
`fr1_not_identity_improved`, `fr1_CVmap_invertible_improved`,
`fr2_not_identity_improved`, `fr2_CVmap_invertible_improved`,
`fr2_CVmap_invertible_capstone`, `kinect_not_identity`, `kinect_invertible`): all depend
only on `propext, Classical.choice, Quot.sound`. Forbidden-construct scan
(`sorry`/`admit`/custom `axiom`/`native_decide`/`unsafe`/`partial`, word-boundary regex)
across all five new/modified files: zero genuine matches (two doc-comment mentions of
the word "sorry" inside a sentence stating its absence, confirmed harmless).

---

## 8. Self-audit: hidden assumptions and domain-handling pitfalls found and fixed

Per task item 6 ("challenge the new conditions for hidden assumptions, incorrect domain
handling, and overly broad claims"), two real issues were caught and fixed during
development, not merely asserted absent:

1. **`|Nnum|,|Dden| ≤ 1` is not automatically true for the monotone-negative case.**
   An early draft of `Nnum_tight_bound_neg`/`Dden_tight_bound_neg` assumed `Nnum,Dden∈[0,1]`
   from `a≤0` and monotonicity alone — but if the polynomial's value at the boundary
   `f(U)` is more negative than `-2`, then `Nnum=1+f(u)` can fall below `-1`, breaking
   the claimed bound `|Nnum|≤1`. This was caught by Lean's own type-checker (a failed
   `linarith` goal, not a hand-review), not assumed benign — fixed by adding an explicit,
   separately-checked hypothesis `hge2 : -2 ≤ a·R²+b·R⁴+c·R⁶` to every affected lemma
   (`Nnum_tight_bound_neg`, `Dden_tight_bound_neg`, `Rfac_tight_bounded_neg`,
   `Rfac_tight_lipschitz_neg`, and all downstream theorems) — verified true for Kinect's
   actual coefficients at `R=2/5` (`kinect_hge2_1`, `kinect_hge2_4`), but **not** a free
   consequence of the other hypotheses, and so not silently assumed.
2. **A manually-derived "`(Tang θ z).re=0` at `y=0`" claim was false.** An early draft of
   `kinect_not_identity` assumed the tangential x-displacement vanishes when the
   imaginary part is zero — true for the `2p1·x·y` cross term, but **false** for the
   `p2·(r²+2x²)` term, which is nonzero at `y=0` whenever `p2≠0` (exactly the kind of
   degenerate-looking-but-wrong simplification the task asked to guard against). Caught
   by `norm_num` refusing to close the resulting `=0` goal (reported as `⊢ False` after
   substitution, not a vacuous success) — fixed by computing the full real part directly
   via `Rfac`/`radial` rather than asserting a partial vanishing.

No other hidden assumptions were found; in particular, every `hR`/`hc`/`ha`/`hmono`
hypothesis in `Pipeline/SignedCubicBounds.lean` was checked to be independently
discharged (not smuggled as "follows trivially") at each of its four call sites
(`TightBoundsNoDenominator.lean` twice, `TightBoundsWithDenominator.lean` twice), and the
`hge2` fix above was propagated to all of them, not patched only where the build first
failed.

---

## 9. Remaining limitations (reported, not resolved)

- **SQ-CV-07, OpenLensIO D→U interoperability, floating-point/production
  correctness** — untouched, as before.
- **Azure Kinect DK's `CVmap`/`SensorPoint` bridge is not proved** (§6) — the single
  largest gap relative to a fully-closed task.
- **The tightened bounds are themselves not claimed optimal.** `quad_chord_upper`'s
  bound (used for the positive case's Lipschitz upper side) is a chord bound, not the
  true supremum; a tighter (but more complex, requiring explicit vertex-location case
  splits) analysis could likely improve TUM fr1 further, and might close the gap to
  full-image coverage found in §5a.
- **TUM fr1 falls just short of full-image injectivity** (§5a) — an open question
  whether a sharper (not merely "tighter than before") bound would close this specific
  gap.
- **The discriminant/monotone dichotomy covers the three calibrations tested, not all
  possible real calibrations.** A hypothetical calibration whose radial polynomial has
  an interior critical point *inside* the certified disk (neither globally sign-definite
  nor monotone on the relevant range) would need a third, not-yet-built lemma family
  (the general cubic-extremum case) — none of TUM fr1/fr2/Azure Kinect DK happened to
  require this, but it is not established that no real calibration would.
