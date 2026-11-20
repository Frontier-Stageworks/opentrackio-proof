# Bounded-Domain Invertibility of the Actual Rational Brown-Conrady Model

Extends the inverse-conjugacy bridge (`audit/INVERSE_CONJUGACY_IMPLEMENTATION.md`) with
genuine, kernel-checked invertibility — not merely conjugacy of an assumed inverse — for
`distortPointCV`/`CVmap`, the **actual 6-coefficient rational Brown-Conrady model with
tangential distortion** used throughout `opencv_opentrackio_proofs/`, on an explicit
bounded 2D disk. LAPS artifacts: `docs/laps/bounded-domain-invertibility/`.

**This does not resolve SQ-CV-07, OpenLensIO native D→U interoperability, or production
correctness.** See §8 before citing anything here as evidence of those.

---

## 1. Executive summary

| Priority (task) | Result |
|---|---|
| 1. Denominator safety from explicit coefficient bounds | **Done** — `denom_pos`/`denom_ge`, condition `denomMargin θ R < 1` |
| 2. Sufficient injectivity + existence conditions via Lipschitz/contraction | **Done** — `RDist_injective_on_disk` and, further, genuine Banach existence/uniqueness `RDist_exists_unique_preimage` |
| 3. Connect to the existing 2D inverse-conjugacy theorem | **Done** — `CVmap_inverse_invOn` discharges `opencv_openlensio_inverse_conjugate`'s `hCVInv` |
| 4. Two nontrivial Lean-verified calibrations, one radial+tangential, positive-radius certified | **Done** — unit-disk examples with `k1=k4=1/10` and `k1=k4=1/10, p1=1/100` |
| 5. Full build, axiom audit, hidden-assumption check | **Done** — 8396 default-build jobs exit 0; every new declaration depends only on standard axioms; one genuine over-broad domain caught and corrected mid-session (§6) |

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
| `Pipeline/RationalDistortionExamples.lean` | `θ₁`, `θ₂`, `example1_denom_safe/contraction/invertible`, `example2_denom_safe/contraction/invertible/CVmap_invertible` |

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
requires (`Set.InvOn cv' (CVmap k1 k2 k3 k4 k5 k6 p1 p2 hden) A B` for some `A B cv'`) —
confirmed by direct inspection of both signatures and by a scratch harness that threads
`example2_CVmap_invertible` into a live application of
`opencv_openlensio_inverse_conjugate`: the only error that remained after fixing an
initial (trivial, missing-argument) type mismatch was two unrelated `norm_num` numeric
side-goals in that throwaway script's own hastily-reused pixel-parameter values, not a
structural incompatibility — see `docs/laps/bounded-domain-invertibility/proof-run-log.md`
Entry 5 for the exact record, including what was and was not re-debugged.

**This is the key upgrade over the prior session's `opencv_openlensio_inverse_conjugate`
(`audit/INVERSE_CONJUGACY_IMPLEMENTATION.md`): `hCVInv` is no longer an unconditionally
free, undischarged hypothesis — it is now DERIVABLE from explicit, checkable coefficient
and radius bounds**, for any calibration satisfying `denomMargin < 1` and `LPert < 1`.

---

## 5. Certified domains for the two examples

| | Example 1 (pure radial) | Example 2 (radial + tangential) |
|---|---|---|
| Coefficients | `k1=k4=1/10`, all else `0` | `k1=k4=1/10`, `p1=1/100`, all else `0` |
| Disk radius `R` | `1` | `1` |
| `denomMargin θ R` | `1/10` | `1/10` |
| `denomMargin θ R < 1`? | **Yes** (margin `0.1`) | **Yes** (margin `0.1`) |
| `LPert θ R` (exact value, `norm_num`-verified `< 1`) | `≈ 0.765` | `≈ 0.865` |
| `LPert θ R < 1`? | **Yes** | **Yes** |
| Certified existence/uniqueness region (`B`) | `{y : ‖y‖ + MPert θ₁ 1 ≤ 1}`, `MPert θ₁ 1 ≈ 0.222` | `{y : ‖y‖ + MPert θ₂ 1 ≤ 1}`, `MPert θ₂ 1 ≈ 0.272` |
| Nonempty? | Yes — `RDist θ₁ 0 = 0` (both radial and tangential terms vanish at the origin), so `0 ∈ B` since `MPert θ₁ 1 < 1` | Yes, same argument |
| Non-identity / non-trivial? | Yes — `k1=k4=1/10 ≠ 0`, genuinely distorting | Yes — additionally `p1=1/100 ≠ 0`, genuine tangential distortion present |

Both calibrations are deliberately **not** the all-zero identity map (explicitly
disallowed by the task) and both have **positive**, explicit, `norm_num`-checked
certified radii — not asserted, computed.

---

## 6. A genuine mathematical correction caught mid-session

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

## 7. Full hypothesis inventory — hidden or unnecessarily strong assumptions?

| Hypothesis | Appears in | Status |
|---|---|---|
| `hR : 0 ≤ R` | everywhere | Structurally necessary (disk radius). |
| `hsafe : denomMargin θ R < 1` | §4.1–4.3 | Explicit, checkable, **sufficient** (not claimed necessary) denominator-safety condition. |
| `hcontract : LPert θ R < 1` | §4.2–4.3 | Explicit, checkable, **sufficient** (not claimed necessary) contraction condition — same "sufficient, not shown necessary" status `InverseApproximation.lean`'s own `hcontract` already carries, for consistency. |
| Domain `{z\|‖z‖≤R ∧ ‖RDist θ z‖+MPert θ R≤R}` vs. plain `{‖z‖≤R}` | `RDist_inverse_invOn`, `CVmap_inverse_invOn` | **Not** a hidden weakening — a *necessary* correction (§6), made maximally visible, not buried. |
| `hden`/`hdenOTI` (CVmap/OTImap's own per-point domain hypotheses) | `CVmap_inverse_invOn` | Pre-existing, inherited from the prior session's `InverseConjugacyApplication.lean` — unchanged here. |
| Bound/Lipschitz constants (`Mrad`, `Lrad`, `RfacUB`, `RfacL`, `RfacDevUB`, `MPert`, `LPert`) | throughout | **Not tight** — these are the same style of conservative, closed-form (not optimized) bounds `InverseApproximation.lean` itself already uses (triangle-inequality-based, not sharp). The TRUE set of `(θ, R)` pairs admitting a certified inverse is almost certainly larger than what `denomMargin < 1 ∧ LPert < 1` captures. This is a real limitation on how large a certified disk this method produces for given coefficients, not a soundness issue. |
| Two-dimensionality / tangential coupling | `RDist`, `Pert` | Both coordinates handled together throughout (`RDist`/`Pert` are single ℂ-valued functions, not independent per-axis results) — confirmed genuinely 2D, not a relabeled 1D result (unlike a risk flagged in the prior session for a different theorem). |

**No hypothesis in this slice assumes the desired conclusion.** `hsafe` and `hcontract`
are stated purely in terms of the coefficients and `R`; they do not mention injectivity,
existence, or invertibility anywhere in their own statement.

---

## 8. What remains explicitly unresolved

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

## 9. Build and axiom summary

```sh
lake build   # plain, default targets — 8396 jobs, exit 0 (was 8391 before this slice)
```

`#print axioms` on all ~31 new declarations: every one depends only on
`propext, Classical.choice, Quot.sound`. Forbidden-construct scan
(`sorry|admit|native_decide|^unsafe|^partial|^\s*axiom\b`) across all 5 new files: zero
matches. `git status`: zero existing files modified.
