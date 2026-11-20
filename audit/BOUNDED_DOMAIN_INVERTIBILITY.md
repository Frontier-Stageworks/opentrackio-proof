# Bounded-Domain Invertibility of the Actual Rational Brown-Conrady Model

Extends the inverse-conjugacy bridge (`audit/INVERSE_CONJUGACY_IMPLEMENTATION.md`) with
genuine, kernel-checked invertibility — not merely conjugacy of an assumed inverse — for
`distortPointCV`/`CVmap`, the **actual 6-coefficient rational Brown-Conrady model with
tangential distortion** used throughout `opencv_opentrackio_proofs/`, on an explicit
bounded 2D disk. LAPS artifacts: `docs/laps/bounded-domain-invertibility/`.

**This does not resolve SQ-CV-07, OpenLensIO native D→U interoperability, or production
correctness.** See §9 before citing anything here as evidence of those.

**CORRECTION NOTICE (second adversarial pass).** The examples originally reported in this
document used `k1 = k4` for both calibrations. Since the radial factor is
`R(u) = (1+k1·u+k2·u²+k3·u³)/(1+k4·u+k5·u²+k6·u³)`, `k1=k4` with all other radial
coefficients zero makes numerator and denominator the identical polynomial, so
`R(u) ≡ 1`. **Example 1 (`p1=p2=0`) was therefore exactly the identity map**, and
Example 2 had tangential distortion only, not "radial and tangential" as originally
claimed. This was a defect in example *design*, not in any proved theorem — every lemma
in §4 remains correct and is unaffected. See §6 for the full account of the error, the
fix, and what was additionally strengthened while correcting it (an explicit non-identity
proof at a concrete point, and a fully-discharged, permanently-committed composition into
`opencv_openlensio_inverse_conjugate` — see §4.3 and §6).

---

## 1. Executive summary

| Priority (task) | Result |
|---|---|
| 1. Denominator safety from explicit coefficient bounds | **Done** — `denom_pos`/`denom_ge`, condition `denomMargin θ R < 1`; for the corrected examples, additionally **discharged globally** (`hden_shared`/`hdenOTI_shared`, §6) rather than left as a free hypothesis |
| 2. Sufficient injectivity + existence conditions via Lipschitz/contraction | **Done** — `RDist_injective_on_disk` and, further, genuine Banach existence/uniqueness `RDist_exists_unique_preimage` |
| 3. Connect to the existing 2D inverse-conjugacy theorem | **Done, and completed as a permanent, fully-resolved theorem** (`example2_full_inverse_conjugate`, §6) — not merely shown type-compatible in a scratch script |
| 4. Two nontrivial Lean-verified calibrations, one radial+tangential, with genuinely nonzero (non-identity) radial distortion, positive-radius certified | **Done after correction** — unit-disk examples with `k1=1/5, k4=1/20` (Example 1) and additionally `p1=1/200` (Example 2), each with an explicit, machine-checked non-identity witness (§5, §6) |
| 5. Full build, axiom audit, hidden-assumption check; discharge global denominator assumptions where possible | **Done** — 8396 default-build jobs exit 0; every declaration depends only on standard axioms; one genuine over-broad domain caught and corrected in the first pass (§7); the identity-map example defect caught and corrected in this second pass (§6); global `hden`/`hdenOTI` now discharged by `positivity`, not merely assumed (§6) |

No proof in this slice was left incomplete. No existing file, definition, or theorem
statement was modified. No axiom was added.

---

## 2. Architecture (why ℂ, why not retrofit InverseApproximation.lean)

`inverse_approximation/InverseApproximation.lean`'s existing `Coeffs`/`Φ`/`D`/`U`
machinery is a **polynomial** (denominator-free) model with a distortion-*strength*
parameter `t`: `D θ t x = x + t•Φ θ x`. The actual pipeline model
(`distortXCV`/`distortYCV`, `OpenCVModel.lean`) is **rational** (has a denominator) and
has **no strength parameter** — the coefficients are already at full strength, and the
radial factor `R(r²) = N(r²)/D(r²)` carries its own `1 +` baseline rather than being
added to a separate identity term. These are genuinely different functional shapes, so
per the task's explicit instruction not to change established definitions, this slice
introduces **new, parallel** definitions (`RCoeffs`, `Nnum`, `Dden`, `Rfac`, `Tang`,
`RDist`, `Pert`) rather than retrofitting the existing ones — while **reusing**, by
direct import and with zero new proof, every piece of `InverseApproximation.lean` that is
generic enough to apply unchanged: `radial_bounded`/`radial_lipschitz` (via dummy
`Coeffs` values with `p1=p2=0`, since those two lemmas depend only on `k1,k2,k3`),
`normSq_lipschitz`/`normSq_sq_lipschitz`/`normSq_cube_lipschitz`, `smul_norm`, and —
most substantially — `phi_bounded`/`phi_lipschitz` for the tangential part, via the
observation that `Φ ⟨0,0,0,p1,p2⟩ z` is *definitionally* the exact tangential
displacement this model needs (verified by direct inspection, not assumed).

Representation: **ℂ**, matching `InverseApproximation.lean`, specifically to make the
above reuse direct (no type conversion needed for the reused lemmas). The final
connection back to the actual `SensorPoint`-based `CVmap`/`distortPointCV` is made via
the equivalence `SensorPoint ≃ ℂ` (`toComplexEquiv`) and `conjugate_invOn`
(`InverseConjugacy.lean`, built in the prior session) — the same general tool
`ForwardConjugacy.lean`'s `screenScaleEquiv` used for coordinate *scaling*, reused here
for representation *relabeling* instead.

---

## 3. New files and exact declarations

| File | Contents |
|---|---|
| `Pipeline/RationalRadialBounds.lean` | `RCoeffs`, `numCoeffs`, `denCoeffs`, `Nnum`, `Dden`, `Nnum_bounded`, `Dden_bounded`, `Nnum_lipschitz`, `Dden_lipschitz`, `denomMargin`, `denomLB`, `denom_ge`, `denom_pos`, `Rfac`, `NnumUB`, `DdenUB`, `Nnum_abs_le`, `Dden_abs_le`, `RfacUB`, `Rfac_bounded`, `RfacL`, `Rfac_lipschitz`, `RfacDevUB`, `Rfac_dev_bounded` |
| `Pipeline/RationalDistortionBounds.lean` | `tangCoeffs`, `Tang`, `Tang_bounded`, `Tang_lipschitz`, `RDist`, `MR`, `LR`, `RDist_bounded`, `RDist_lipschitz`, `Pert`, `RDist_eq_add_Pert`, `MPert`, `LPert`, `Pert_bounded`, `Pert_lipschitz` |
| `Pipeline/RationalDistortionInjectivity.lean` | `inverseStepR`, `inverseStepR_maps_disk`, `inverseStepR_lipschitz`, `RDist_eq_implies_eq`, `RDist_injective_on_disk`, `MPert_nonneg`, `LPert_nonneg`, `RDist_exists_unique_preimage` |
| `Pipeline/RationalDistortionBridge.lean` | `toComplexEquiv`, `RCoeffsOf`, `CVmap_eq_RDist`, `RDistInv`, `RDist_inverse_invOn`, `CVmap_inverse_invOn` |
| `Pipeline/RationalDistortionExamples.lean` | `θ₁`, `θ₂`, `hden_shared`, `hdenOTI_shared`, `example1_denom_safe/contraction/not_identity/invertible`, `example2_denom_safe/contraction/not_identity/tangential_active/invertible/CVmap_invertible/full_inverse_conjugate` |

All under `opencv_opentrackio_proofs/Pipeline/`, automatically covered by
`PipelineEquivalence`'s existing `globs = ["PipelineEquivalence", "Pipeline.+"]` — no
`lakefile.toml` change was needed for this slice (confirmed: default-build job count rose
from 8391 to 8396, exactly 5).

---

## 4. Exact theorem statements

### 4.1 Denominator safety

```lean
noncomputable def denomMargin (θ : RCoeffs) (R : ℝ) : ℝ := Mrad (denCoeffs θ) R
  -- = |θ.k4|·R² + |θ.k5|·R⁴ + |θ.k6|·R⁶

noncomputable def denomLB (θ : RCoeffs) (R : ℝ) : ℝ := 1 - denomMargin θ R

theorem denom_pos (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (z : ℂ) (hz : ‖z‖ ≤ R) :
    0 < Dden θ z
```

This is the explicit, checkable, coefficient-and-radius-only condition the task's first
priority asked for: `|k4|R²+|k5|R⁴+|k6|R⁶ < 1` guarantees the denominator stays bounded
away from zero (below by `1 - that margin`) everywhere on the disk `‖z‖≤R`.

### 4.2 Injectivity and TRUE existence/uniqueness (the hardest result)

```lean
theorem RDist_injective_on_disk (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (hcontract : LPert θ R < 1) :
    Set.InjOn (RDist θ) {z : ℂ | ‖z‖ ≤ R}

theorem RDist_exists_unique_preimage
    (θ : RCoeffs) (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin θ R < 1) (hcontract : LPert θ R < 1)
    (y : ℂ) (hy : ‖y‖ + MPert θ R ≤ R) :
    ∃! z : ℂ, ‖z‖ ≤ R ∧ RDist θ z = y
```

`LPert θ R` is an explicit, fully computable closed-form expression in the 8 coefficients
and `R` (built from `RfacDevUB`, `RfacL`, and `InverseApproximation.lean`'s own `L`):

```lean
noncomputable def LPert (θ : RCoeffs) (R : ℝ) : ℝ :=
  RfacDevUB θ R + RfacL θ R * R + L (tangCoeffs θ) R
```

`RDist_exists_unique_preimage` is **genuine existence and uniqueness of the true
inverse**, via Mathlib's Banach fixed-point theorem (`ContractingWith.exists_fixedPoint'`)
applied to the Picard iteration `inverseStepR θ y z = y - Pert θ z` — not an assumed or
merely-injective result, and not restricted to the simplified polynomial model: this is
the actual 6-coefficient rational radial factor together with the actual 2-coefficient
tangential displacement, exactly as they appear in `distortXCV`/`distortYCV`.

### 4.3 Connection to the existing 2D inverse-conjugacy theorem

```lean
theorem CVmap_inverse_invOn
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (hden : ∀ x' y' : ℝ, 1+k4*(x'^2+y'^2)+k5*(x'^2+y'^2)^2+k6*(x'^2+y'^2)^3 ≠ 0)
    (R : ℝ) (hR : 0 ≤ R)
    (hsafe : denomMargin (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) R < 1)
    (hcontract : LPert (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) R < 1) :
    Set.InvOn
      (toComplexEquiv.symm ∘ RDistInv (RCoeffsOf k1 k2 k3 k4 k5 k6 p1 p2) R hR hsafe hcontract
        ∘ toComplexEquiv)
      (CVmap k1 k2 k3 k4 k5 k6 p1 p2 hden)
      (toComplexEquiv.symm '' {z : ℂ | ‖z‖ ≤ R ∧ ‖RDist θ z‖ + MPert θ R ≤ R})
      (toComplexEquiv.symm '' {y : ℂ | ‖y‖ + MPert θ R ≤ R})
```

This has **exactly** the type `opencv_openlensio_inverse_conjugate`'s `hCVInv` parameter
requires (`Set.InvOn cv' (CVmap k1 k2 k3 k4 k5 k6 p1 p2 hden) A B` for some `A B cv'`).

**Correction (second adversarial pass): this is no longer only shown type-compatible in a
scratch harness.** `Pipeline/RationalDistortionExamples.lean` now contains
`example2_full_inverse_conjugate`, a **permanently committed, fully-resolved** theorem
(every hypothesis closed by `norm_num`/`positivity`, no step left as a throwaway check)
that applies `opencv_openlensio_inverse_conjugate` directly with `example2_CVmap_invertible`
as its `hCVInv` argument, for a concrete pixel-level calibration
(`F=2, fx=fy=1, w=2, ws=1, h=2, h_shader=1, cx=cy=0`) consistent with Example 2's
coefficients. See §6.

**This is the key upgrade over the prior session's `opencv_openlensio_inverse_conjugate`
(`audit/INVERSE_CONJUGACY_IMPLEMENTATION.md`): `hCVInv` is no longer an unconditionally
free, undischarged hypothesis — it is now DERIVABLE from explicit, checkable coefficient
and radius bounds**, for any calibration satisfying `denomMargin < 1` and `LPert < 1`.

---

## 5. Certified domains for the two examples (corrected coefficients)

| | Example 1 (pure radial) | Example 2 (radial + tangential) |
|---|---|---|
| Coefficients | `k1=1/5, k4=1/20`, all else `0` | `k1=1/5, k4=1/20, p1=1/200`, all else `0` |
| Disk radius `R` | `1` | `1` |
| `denomMargin θ R` | `1/20` | `1/20` |
| `denomMargin θ R < 1`? | **Yes** (margin `0.05`) | **Yes** (margin `0.05`) |
| `LPert θ R` (exact value, `norm_num`-verified `< 1`) | `5/19 + 216/361 ≈ 0.861` | `≈ 0.911` |
| `LPert θ R < 1`? | **Yes** | **Yes** |
| Certified existence/uniqueness region (`B`) | `{y : ‖y‖ + MPert θ₁ 1 ≤ 1}`, `MPert θ₁ 1 = 5/19 ≈ 0.263` | `{y : ‖y‖ + MPert θ₂ 1 ≤ 1}`, `MPert θ₂ 1 ≈ 0.288` |
| Nonempty? | Yes — `RDist θ₁ 0 = 0`, so `0 ∈ B` since `MPert θ₁ 1 < 1` | Yes, same argument |
| **Genuinely non-identity?** | **Yes — proved, not asserted**: `example1_not_identity` computes `CVmap(...)⟨1,0⟩ = ⟨8/7, 0⟩ ≠ ⟨1,0⟩` (since `k1≠k4` makes `R(1)=(1+1/5)/(1+1/20)=8/7≠1`) | **Yes — proved at two points**: `example2_not_identity` (same radial witness, `(1,0)↦(8/7,·)`) AND `example2_tangential_active`, which proves the Example-2 map disagrees with the *pure-radial-only* map at `(1,1)` — isolating the tangential contribution specifically, not merely asserting `p1≠0` |
| Global `hden`/`hdenOTI` discharged? | **Yes** — `hden_shared`, proved by `positivity` for all real inputs (since `k4=1/20>0`, `k2=k3=k5=k6=0`) | **Yes** — same `hden_shared`; OTI-side `hdenOTI_shared` also discharged (`l2=k4/F²=1/80>0`) |

Both calibrations are deliberately **not** the all-zero identity map, and this time that
is a **proved** fact (§6), not merely a coefficient-nonzero claim. Both have **positive**,
explicit, `norm_num`-checked certified radii — not asserted, computed.

---

## 6. The identity-map example defect: full account (second adversarial pass)

**The error.** The original Examples 1 and 2 both set `k1 = k4 = 1/10` (with
`k2=k3=k5=k6=0`). The radial factor is
`R(u) = (1+k1·u+k2·u²+k3·u³) / (1+k4·u+k5·u²+k6·u³)`; with `k1=k4` and all higher
coefficients zero, numerator and denominator are the *same* polynomial `1+0.1u`, so
`R(u) = 1` for every `u ≥ 0` — an identity, not an approximation. Example 1 additionally
had `p1=p2=0`, so `distortXCV = R(u)·x + 0 = x` and `distortYCV = y`: **Example 1 was the
exact identity map**, which the task's own restriction ("do not manufacture an example by
choosing only the identity distortion map") explicitly rules out. Example 2 added
`p1=1/100` but kept `k1=k4`, so it exercised the tangential machinery only, not "radial
and tangential" as the document claimed. This was caught by the user, not by this
project's own review in the first pass — a real gap in that review's thoroughness,
recorded here rather than minimized.

**Root cause.** The coefficients were chosen to make `denomMargin`/`LPert` easy to
estimate by hand, without checking what `R(u)` reduces to algebraically. No proved lemma
was affected — `Rfac_bounded`, `Rfac_lipschitz`, `RDist_exists_unique_preimage`, etc. are
all correct and unaffected; only the numeric *instantiation* was defective.

**The fix.** New coefficients: `k1=1/5, k4=1/20` for both examples (genuinely different,
so `R(u)` is not identically 1), `p1=1/200` added for Example 2 only. Both examples now
include an explicit, machine-checked **non-identity theorem**:

```lean
theorem example1_not_identity :
    CVmap (1/5) 0 0 (1/20) 0 0 0 0 hden_shared (⟨1, 0⟩ : SensorPoint)
      ≠ (⟨1, 0⟩ : SensorPoint)
```

proved by computing `sensorRadius ⟨1,0⟩ = 1` and reducing `distortXCV`'s value to the
exact rational `(1+1/5)/(1+1/20) = 8/7`, then `8/7 ≠ 1` by `norm_num` — not by asserting
the coefficients are nonzero and stopping there. Example 2 adds a second theorem,
`example2_tangential_active`, proving the Example-2 map (`p1=1/200`) disagrees with the
*pure-radial* map (same `k1,k4`, `p1=0`) at the point `(1,1)` — a direct, isolated witness
that the tangential coefficient is doing real work, not merely present in the parameter
list.

**What was additionally strengthened while fixing this (task items 4–5):**

- **Task item 4 (completed composition, not scratch)**: `example2_full_inverse_conjugate`
  is now a permanent, fully-resolved theorem in `RationalDistortionExamples.lean`
  (verbatim statement in §4.3) applying `opencv_openlensio_inverse_conjugate` with
  `example2_CVmap_invertible` as `hCVInv`, every one of its ~20 hypotheses discharged by
  `norm_num`/`positivity` in the committed file — not left as an unresolved scratch check
  the way the first pass's end-to-end verification was.
- **Task item 5 (discharge global denominator assumptions)**: `hden_shared` and
  `hdenOTI_shared` prove the CV-side and OTI-side denominator-nonzero conditions **for
  every real input, unconditionally** (not merely within the certified disk), since
  `k4=1/20>0` and `l2=k4/F²=1/80>0` with all other denominator coefficients zero make
  `1 + (positive)·(x'²+y'²) ≥ 1 > 0` directly, closed by `positivity` alone. This is
  strictly stronger than what the task asked to "identify" — it is a full discharge, not
  merely a flagged gap.

**Verification record**: `lake build Pipeline.RationalDistortionExamples` — succeeds on
the corrected file (full output and iteration history in
`docs/laps/bounded-domain-invertibility/proof-run-log.md` Entry 6); `#print axioms` on
every declaration in the corrected file (`hden_shared` through
`example2_full_inverse_conjugate`) — all depend only on
`propext, Classical.choice, Quot.sound`; forbidden-construct scan — zero genuine matches
(one substring false-positive, "admitted" containing "admit", found and corrected in the
file's own prose to avoid future confusion, not a real forbidden construct).

---

## 7. A genuine mathematical correction caught mid-session (first adversarial pass)

The first draft of `RDist_inverse_invOn` claimed `Set.InvOn ... {z | ‖z‖≤R} {y | ...}` —
i.e. that the LEFT inverse property holds on the **entire disk**. This is **false in
general**: a point `z` in the disk need not have `RDist θ z` land in the smaller buffer
region `B` where the Banach-constructed inverse is actually characterized; outside `B`,
the constructed inverse function is unspecified junk (`0`), by explicit construction
(mirroring `Function.invFun`'s junk-value discipline, per the task's own caution about
this). `linarith` failed to derive the needed bound from the available hypotheses —
correctly, since no such bound exists in general. The fix was **not** to weaken the
conclusion or add an unjustified hypothesis, but to correct the domain to the
mathematically accurate set:

```lean
{z : ℂ | ‖z‖ ≤ R ∧ ‖RDist θ z‖ + MPert θ R ≤ R}
```

i.e., the subset of the disk whose **image** also lands in the buffer. This is reported
here explicitly because it is exactly the kind of error a less careful pass could have
silently "fixed" by weakening `Set.InjOn`-only claims or by smuggling in an unjustified
image-containment assumption; instead the correct, slightly more complex domain is used
throughout, visible in every downstream statement (§4.2, §4.3) that depends on it.

---

## 8. Full hypothesis inventory — hidden or unnecessarily strong assumptions?

| Hypothesis | Appears in | Status |
|---|---|---|
| `hR : 0 ≤ R` | everywhere | Structurally necessary (disk radius). |
| `hsafe : denomMargin θ R < 1` | §4.1–4.3 | Explicit, checkable, **sufficient** (not claimed necessary) denominator-safety condition. |
| `hcontract : LPert θ R < 1` | §4.2–4.3 | Explicit, checkable, **sufficient** (not claimed necessary) contraction condition — same "sufficient, not shown necessary" status `InverseApproximation.lean`'s own `hcontract` already carries, for consistency. |
| Domain `{z\|‖z‖≤R ∧ ‖RDist θ z‖+MPert θ R≤R}` vs. plain `{‖z‖≤R}` | `RDist_inverse_invOn`, `CVmap_inverse_invOn` | **Not** a hidden weakening — a *necessary* correction (§7), made maximally visible, not buried. |
| `hden`/`hdenOTI` (CVmap/OTImap's own per-point domain hypotheses) | `CVmap_inverse_invOn` | Pre-existing, inherited from the prior session's `InverseConjugacyApplication.lean` — unchanged here. |
| Bound/Lipschitz constants (`Mrad`, `Lrad`, `RfacUB`, `RfacL`, `RfacDevUB`, `MPert`, `LPert`) | throughout | **Not tight** — these are the same style of conservative, closed-form (not optimized) bounds `InverseApproximation.lean` itself already uses (triangle-inequality-based, not sharp). The TRUE set of `(θ, R)` pairs admitting a certified inverse is almost certainly larger than what `denomMargin < 1 ∧ LPert < 1` captures. This is a real limitation on how large a certified disk this method produces for given coefficients, not a soundness issue. |
| Two-dimensionality / tangential coupling | `RDist`, `Pert` | Both coordinates handled together throughout (`RDist`/`Pert` are single ℂ-valued functions, not independent per-axis results) — confirmed genuinely 2D, not a relabeled 1D result (unlike a risk flagged in the prior session for a different theorem). |

**No hypothesis in this slice assumes the desired conclusion.** `hsafe` and `hcontract`
are stated purely in terms of the coefficients and `R`; they do not mention injectivity,
existence, or invertibility anywhere in their own statement.

---

## 9. What remains explicitly unresolved

Unchanged from the prior session, restated for this slice specifically:

- **OpenLensIO's native D→U undistortion function `U`** (`openlensio_semantics/DistortionModel.lean`'s
  `undistortPoint`, operating on `RadialCoefficients`/`TangentialCoefficients` — a
  different coefficient structure entirely) is not mentioned, used, or claimed equal to
  anything in this slice.
- **No finite inverse-coefficient set is constructed or claimed to exist** — this slice
  proves existence/uniqueness of the true inverse as a *function* (via Banach), not a
  closed-form Brown-Conrady-shaped formula for it; `audit/DISTORTION_DIRECTION_INTEROPERABILITY.md`
  §7's impossibility result (no exact rational-function inverse exists in general) is
  untouched and still applies.
- **No claim that any real consumer numerically computes this inverse correctly** — the
  existence proof is nonconstructive (via `Classical.choice` inside Mathlib's Banach
  argument), not an algorithm.
- **No floating-point/implementation claim whatsoever.**
- **SQ-CV-07 is not resolved** — this slice strengthens the mathematical machinery
  available for a FUTURE argument connecting to native `U`, but does not attempt that
  connection itself.

## 10. Build and axiom summary

```sh
lake build   # plain, default targets — 8396 jobs, exit 0 (unchanged job count: this
             # correction pass only edited the content of an already-counted file, it
             # did not add new ones)
```

`#print axioms` on all ~37 declarations across the 5 files (31 from the first pass plus
`hden_shared`, `hdenOTI_shared`, `example1_not_identity`, `example2_not_identity`,
`example2_tangential_active`, `example2_full_inverse_conjugate` added in this correction
pass): every one depends only on `propext, Classical.choice, Quot.sound`.
Word-boundary-aware forbidden-construct scan (`\bsorry\b|\badmit\b|native_decide|^unsafe|^partial|^\s*axiom\b`)
across all 5 files: zero genuine matches (one substring false-positive from the word
"admitted" in prose, fixed). `git status`: zero *existing, previously-committed* files
modified beyond `RationalDistortionExamples.lean` itself (the one file this correction
pass edited) and this audit document; no established definition or already-proved
theorem statement from the first pass was changed.
