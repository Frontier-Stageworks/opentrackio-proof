# Inverse-Conjugacy Bridge: Implementation Report

Implements Candidate 2 from `audit/DISTORTION_DIRECTION_INTEROPERABILITY.md` §8: the
smallest meaningful theorem connecting the existing OpenCV/OpenTrackIO forward-map
conjugacy to a genuine statement about their mathematical inverses. LAPS artifacts for
this slice: `docs/laps/inverse-conjugacy-bridge/` (proof-capsule, proof-plan, proof-run-log,
proof-review).

**This does not resolve SQ-CV-07.** See §7 ("What this does not establish") before citing
any result below as evidence of OpenTrackIO/OpenLensIO interoperability.

---

## 1. New files and declarations

| File | Declarations | Role |
|---|---|---|
| `opencv_opentrackio_proofs/Pipeline/OpenTrackIOModel.lean` | `distortXOTI`, `distortYOTI`, `distortPointOTI` | Names the OpenTrackIO-side forward map used inline in `PixelIffCorrected.lean` (confirmed: that file never calls a named function for the OTI side). Same formula shape as `distortXCV`/`distortYCV`/`distortPointCV`, `l,q` in place of `k,p`. |
| `opencv_opentrackio_proofs/Pipeline/PixelIffCorrectedY.lean` | `opencv_openlensio_full_pipeline_pixel_corrected_y` | **New proof obligation**: the y-axis analogue of `opencv_openlensio_full_pipeline_pixel_corrected`, under the corrected `q=p/F` scaling. No such theorem existed anywhere before this slice (the existing Y-axis work mirrors only the as-published `q=p/F²` family). |
| `opencv_opentrackio_proofs/Pipeline/ForwardConjugacy.lean` | `ScreenScale`, `opencv_openlensio_forward_point_corrected` | The genuine two-dimensional, composed-function forward conjugacy, derived from the x and y pixel theorems. |
| `opencv_opentrackio_proofs/InverseConjugacy.lean` | `conjugate_invOn` | The abstract, model-independent conjugacy-of-inverses lemma. No project-specific import. |
| `opencv_opentrackio_proofs/Pipeline/InverseConjugacyApplication.lean` | `denom_sensorRadius_ne_zero`, `CVmap`, `OTImap`, `screenScaleEquiv`, `opencv_openlensio_inverse_conjugate` | Specializes the abstract lemma to the actual OpenCV/OpenTrackIO maps. |
| `opencv_opentrackio_proofs/Pipeline/InverseConjugacyExample.lean` | one `example` | Concrete, non-identity, nonzero-coefficient numeric instantiation, kernel-checked. |

**No existing file was modified.** Confirmed by `git diff --stat` returning empty for
every file the task named off-limits: `PixelIff.lean`, `PixelIffHelpers.lean`,
`PixelSufficiency.lean`, `PixelIffCorrected.lean`, `DistortionConversion.lean`,
`DistortionConversionCorrected.lean`, `OpenCVModel.lean`, `PixelIffY.lean`,
`PixelIffHelpersY.lean`, `PixelSufficiencyY.lean`.

`lakefile.toml`: registered `InverseConjugacy` as a new `[[lean_lib]]` target (the other
five new files are automatically covered by `PipelineEquivalence`'s existing
`globs = ["PipelineEquivalence", "Pipeline.+"]`, since they live under `Pipeline/`).

---

## 2. Exact theorem statements

### 2.1 The new y-component pixel theorem (prerequisite)

```lean
theorem opencv_openlensio_full_pipeline_pixel_corrected_y
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fy cy h_shader h F ΔPy : ℝ)
    (hh : h ≠ 0) (hhs : h_shader ≠ 0) (hF : F ≠ 0)
    (hl1 : l1 = k1 / F ^ 2) (hl3 : l3 = k2 / F ^ 4) (hl5 : l5 = k3 / F ^ 6)
    (hl2 : l2 = k4 / F ^ 2) (hl4 : l4 = k5 / F ^ 4) (hl6 : l6 = k6 / F ^ 6)
    (hq1 : q1 = p1 / F) (hq2 : q2 = p2 / F)
    (hF_eq : F = (h / h_shader) * fy) (hΔPy : ΔPy = (h / h_shader) * (cy - h_shader / 2))
    (hden : ∀ x' y' : ℝ,
        1 + k4 * (x' ^ 2 + y' ^ 2) + k5 * (x' ^ 2 + y' ^ 2) ^ 2
          + k6 * (x' ^ 2 + y' ^ 2) ^ 3 ≠ 0) :
    ∀ x' y' : ℝ,
      fy * (⟨radial ratio⟩ * y' + p1 * (x'^2+y'^2+2y'^2) + 2*p2*x'*y') + cy
      = (h_shader / h) * (⟨OTI radial ratio at (F x', F y')⟩ * (F*y')
          + q1 * ((Fx')^2+(Fy')^2+2(Fy')^2) + 2*q2*(Fx')*(Fy') + ΔPy)
      + h_shader / 2
```

(full bracketed radial expressions identical in shape to the existing x-theorem; see the
file for the exact, unabbreviated statement — reproduced here abbreviated only for
readability in this report, not as the committed text).

### 2.2 The two-dimensional forward conjugacy (Step 3)

```lean
noncomputable def ScreenScale (F : ℝ) (ε : SensorPoint) : SensorPoint :=
  ⟨F * ε.x, F * ε.y⟩

theorem opencv_openlensio_forward_point_corrected
    (k1 k2 k3 k4 k5 k6 p1 p2 l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fx fy cx cy ws w h_shader h F ΔPx ΔPy : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0) (hh : h ≠ 0) (hhs : h_shader ≠ 0)
    (hF : F ≠ 0) (hF_pos : 0 < F)
    (hl1 : l1 = k1/F^2) (hl3 : l3 = k2/F^4) (hl5 : l5 = k3/F^6)
    (hl2 : l2 = k4/F^2) (hl4 : l4 = k5/F^4) (hl6 : l6 = k6/F^6)
    (hq1 : q1 = p1/F) (hq2 : q2 = p2/F)
    (hF_eq_x : F = (w/ws)*fx) (hF_eq_y : F = (h/h_shader)*fy)
    (hΔPx : ΔPx = (w/ws)*(cx-ws/2)) (hΔPy : ΔPy = (h/h_shader)*(cy-h_shader/2))
    (hden : ∀ x' y' : ℝ, 1+k4*(x'^2+y'^2)+k5*(x'^2+y'^2)^2+k6*(x'^2+y'^2)^3 ≠ 0)
    (ε : SensorPoint)
    (hden_cv : 1+k4*(sensorRadius ε)^2+k5*(sensorRadius ε)^4+k6*(sensorRadius ε)^6 ≠ 0)
    (hden_oti : 1+l2*(sensorRadius (ScreenScale F ε))^2
                 +l4*(sensorRadius (ScreenScale F ε))^4
                 +l6*(sensorRadius (ScreenScale F ε))^6 ≠ 0) :
    distortPointOTI l1 l2 l3 l4 l5 l6 q1 q2 (ScreenScale F ε) hden_oti
      = ScreenScale F (distortPointCV k1 k2 k3 k4 k5 k6 p1 p2 ε hden_cv)
```

**This is the pointwise form of `D_OTI ∘ S_F = S_F ∘ D_CV`** (equivalently
`D_OTI = S_F ∘ D_CV ∘ S_F⁻¹`, since `S_F = ScreenScale F` is invertible — see §2.4). It is
a genuine `SensorPoint` equality (**both coordinates at once**, via `SensorPoint.ext`
internally), proved — not assumed — from `opencv_openlensio_full_pipeline_pixel_corrected`
(x) and the new `opencv_openlensio_full_pipeline_pixel_corrected_y` (y) by algebraically
unwrapping the shared pixel-level offset/scale (`principal_offset_cancels`-style identities,
reproduced locally; `mul_left_cancel₀` to cancel the nonzero `ws/w`/`h_shader/h` factor).

**Confirmed two-dimensional, not a relabeled one-dimensional result**: the statement's
conclusion is a single `SensorPoint` equality that the proof establishes via
`apply SensorPoint.ext` into two genuinely separate sub-proofs, one invoking the x-pixel
theorem and one invoking the new y-pixel theorem — neither component is derived from the
other or assumed from symmetry.

### 2.3 The abstract inverse-conjugacy lemma (Step 4)

```lean
theorem conjugate_invOn {α β : Type*} (S : α ≃ β) (f f' : α → α) (g : β → β)
    (A B : Set α)
    (hconj : ∀ x : α, g (S x) = S (f x))
    (hf' : Set.InvOn f' f A B) :
    Set.InvOn (S ∘ f' ∘ S.symm) g (S '' A) (S '' B)
```

No project import. Depends only on `Quot.sound` (confirmed by `#print axioms`, §5) — the
proof is pure `Equiv`/`Set.InvOn` manipulation, no real-number reasoning at all.

### 2.4 The specialized inverse-conjugacy theorem (Step 5)

```lean
noncomputable def screenScaleEquiv (F : ℝ) (hF : F ≠ 0) : SensorPoint ≃ SensorPoint where
  toFun := ScreenScale F
  invFun := ScreenScale F⁻¹
  left_inv := ...   -- field_simp, using hF
  right_inv := ...  -- field_simp, using hF

noncomputable def CVmap (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (hden : ∀ x' y' : ℝ, 1+k4*(x'^2+y'^2)+k5*(x'^2+y'^2)^2+k6*(x'^2+y'^2)^3 ≠ 0) :
    SensorPoint → SensorPoint :=
  fun ε => distortPointCV k1 k2 k3 k4 k5 k6 p1 p2 ε (denom_sensorRadius_ne_zero k4 k5 k6 hden ε)

noncomputable def OTImap (l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (hdenOTI : ∀ x' y' : ℝ, 1+l2*(x'^2+y'^2)+l4*(x'^2+y'^2)^2+l6*(x'^2+y'^2)^3 ≠ 0) :
    SensorPoint → SensorPoint :=
  fun ε => distortPointOTI l1 l2 l3 l4 l5 l6 q1 q2 ε (denom_sensorRadius_ne_zero l2 l4 l6 hdenOTI ε)

theorem opencv_openlensio_inverse_conjugate
    (k1 k2 k3 k4 k5 k6 p1 p2 l1 l2 l3 l4 l5 l6 q1 q2 : ℝ)
    (fx fy cx cy ws w h_shader h F ΔPx ΔPy : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0) (hh : h ≠ 0) (hhs : h_shader ≠ 0)
    (hF : F ≠ 0) (hF_pos : 0 < F)
    (hl1 : l1 = k1/F^2) (hl3 : l3 = k2/F^4) (hl5 : l5 = k3/F^6)
    (hl2 : l2 = k4/F^2) (hl4 : l4 = k5/F^4) (hl6 : l6 = k6/F^6)
    (hq1 : q1 = p1/F) (hq2 : q2 = p2/F)
    (hF_eq_x : F = (w/ws)*fx) (hF_eq_y : F = (h/h_shader)*fy)
    (hΔPx : ΔPx = (w/ws)*(cx-ws/2)) (hΔPy : ΔPy = (h/h_shader)*(cy-h_shader/2))
    (hden : ∀ x' y' : ℝ, 1+k4*(x'^2+y'^2)+k5*(x'^2+y'^2)^2+k6*(x'^2+y'^2)^3 ≠ 0)
    (hdenOTI : ∀ x' y' : ℝ, 1+l2*(x'^2+y'^2)+l4*(x'^2+y'^2)^2+l6*(x'^2+y'^2)^3 ≠ 0)
    (A B : Set SensorPoint) (cv' : SensorPoint → SensorPoint)
    (hCVInv : Set.InvOn cv' (CVmap k1 k2 k3 k4 k5 k6 p1 p2 hden) A B) :
    Set.InvOn ((screenScaleEquiv F hF) ∘ cv' ∘ (screenScaleEquiv F hF).symm)
      (OTImap l1 l2 l3 l4 l5 l6 q1 q2 hdenOTI)
      (screenScaleEquiv F hF '' A) (screenScaleEquiv F hF '' B)
```

**In words**: if `cv'` is a genuine two-sided inverse of OpenCV's forward distortion map on
sets `A` (domain) and `B` (range), then the `F`-conjugated map
`screenScaleEquiv F hF ∘ cv' ∘ (screenScaleEquiv F hF).symm` is a genuine two-sided inverse
of OpenTrackIO's (corrected) forward distortion map on the correspondingly scaled sets
`screenScaleEquiv F hF '' A`, `screenScaleEquiv F hF '' B`.

---

## 3. Existing results reused (not restated)

- `opencv_openlensio_full_pipeline_pixel_corrected` (`PixelIffCorrected.lean:71-132`) —
  invoked directly inside `opencv_openlensio_forward_point_corrected`'s proof for the x
  component; not re-proved.
- `distortXCV`/`distortYCV`/`distortPointCV` (`OpenCVModel.lean:41-83`) — used as-is as the
  CV-side forward map throughout; no modification.
- `SensorPoint`, `sensorRadius` (`CoordinateTypes.lean:26-35`) — reused via the existing
  import chain already present in `OpenCVModel.lean` (no new heavy dependency introduced).
- `Real.sq_sqrt`, `Equiv.symm_apply_apply`, `mul_left_cancel₀`, `div_ne_zero`,
  `right_ne_zero_of_mul`, `pow_ne_zero` — standard Mathlib lemmas, used by name (not
  guessed; each is a well-known, commonly-cited lemma already used elsewhere in this
  repository's own proofs for the same purpose).

## 4. Build commands and results

```sh
lake build Pipeline.OpenTrackIOModel                        # 3290 jobs, exit 0
lake build Pipeline.PixelIffCorrectedY                       # 3287 jobs, exit 0
lake build Pipeline.ForwardConjugacy                          # 3294 jobs, exit 0
lake build InverseConjugacy                                   # 388 jobs, exit 0
lake build Pipeline.InverseConjugacyApplication                # 3296 jobs, exit 0
lake build Pipeline.InverseConjugacyExample                    # 3297 jobs, exit 0
lake build   # plain, default targets (now fixed — see Phase 2 below)   # 8391 jobs, exit 0
```

All succeed. No warnings in any of the six new files (one pre-existing lint
iteration — a `<;>` vs `;` suggestion in `InverseConjugacyExample.lean` and a
wrong-rewrite-order error in `ForwardConjugacy.lean` — were both fixed during development;
see `docs/laps/inverse-conjugacy-bridge/proof-run-log.md` for the exact failure-and-fix
record of both, plus the two argument-value bugs caught and fixed in the numeric example).

## 5. Axiom dependencies

```
opencv_openlensio_full_pipeline_pixel_corrected_y  → [propext, Classical.choice, Quot.sound]
distortXOTI                                        → [propext, Classical.choice, Quot.sound]
opencv_openlensio_forward_point_corrected          → [propext, Classical.choice, Quot.sound]
conjugate_invOn                                    → [Quot.sound]            ← pure function/set theory
denom_sensorRadius_ne_zero                         → [propext, Classical.choice, Quot.sound]
screenScaleEquiv                                   → [propext, Classical.choice, Quot.sound]
opencv_openlensio_inverse_conjugate                → [propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, or `partial` anywhere
(`grep -nE "sorry|admit|native_decide|^unsafe|^partial|^\s*axiom\b"` across all six new
files: zero matches). Every axiom above is a standard Lean/Mathlib foundational axiom,
present throughout the rest of this repository.

## 6. Hypothesis inventory for `opencv_openlensio_inverse_conjugate`

| Hypothesis | Status |
|---|---|
| `hw, hws, hh, hhs, hF` (nonzero) | structurally necessary and trivial — denominators/scale factors |
| `hF_pos` | carried from the reused x-pixel theorem; not used in this slice's own new proof content either (same as the pre-existing theorem it is threaded from) |
| `hl1..hl6` (radial conversion) | proved-and-discharged **as a hypothesis role**: these are the *given* conversion relations the whole pipeline family is conditioned on (unchanged from all existing pipeline theorems); not re-derived here, but not a new undischarged gap either — identical status to every existing theorem in this repository |
| `hq1, hq2` (corrected tangential, `q=p/F`) | same role as above, now independently supported by `audit/DISTORTION_DIRECTION_INTEROPERABILITY.md` §7's dimensional analysis |
| `hF_eq_x, hF_eq_y` (shared single `F`) | structurally necessary for a genuine single-scale 2D statement (§2.2); stated directly rather than derived from `single_focal_length_compatibility` (deliberately out of scope) |
| `hΔPx, hΔPy` | proved-and-discharged within the proof via `principal_offset_cancels`-style local algebra |
| `hden, hdenOTI` | caller-supplied, free, universally-quantified domain conditions — same pattern as every existing pipeline theorem; not newly introduced risk |
| `A, B : Set SensorPoint`, `cv' : SensorPoint → SensorPoint` | caller-supplied witnesses — no claim they are nonempty or well-chosen beyond what `hCVInv` asserts |
| **`hCVInv : Set.InvOn cv' (CVmap ...) A B`** | **caller-supplied and undischarged.** The one substantive open hypothesis in the entire slice. No theorem in this repository proves this for `distortPointCV`/`CVmap` on any `A, B` — `InjectivityModel.lean`'s results are for `undistortPoint`/`RadialCoefficients`, a different function over a different type. Flagged explicitly in the theorem's own doc-comment, not hidden. |

## 7. What this does and does not establish

**Established, kernel-checked:**
- A genuine two-dimensional forward conjugacy between OpenCV's and OpenTrackIO's
  (corrected) distortion maps (§2.2), derived from both axes' pixel-level theorems.
- A general, model-independent fact: conjugating a partial inverse under a bijective
  coordinate change gives the correspondingly conjugated partial inverse of the conjugated
  function (§2.3).
- The specialization of that fact to the actual `distortPointCV`/`distortPointOTI` (§2.4),
  conditional on an honestly-flagged, undischarged invertibility hypothesis on
  `distortPointCV`.
- A concrete, non-identity, nonzero-coefficient (`k1=1, p1=1`), nonzero-`F` (`F=2≠1`)
  instantiation showing `hCVInv` is satisfiable — via a singleton-set witness, not an open
  domain (§8).

**Not established — stated explicitly, per the task's restrictions, and reproduced from
the theorem's own doc-comment:**
- That OpenLensIO's independently-parameterized **native** `U` (`undistortPoint`,
  `openlensio_semantics/DistortionModel.lean`, a different coefficient structure
  entirely) equals this exact inverse, or bears any proved relationship to it at all.
- That a finite inverse Brown-Conrady coefficient set exists in general — it provably does
  not, for non-degenerate distortion, per
  `audit/DISTORTION_DIRECTION_INTEROPERABILITY.md` §7 ("Test A, extended").
- That any real consumer numerically computes this inverse correctly, or at all.
- That floating-point evaluation of anything here is certified.
- That OpenTrackIO interoperability (SQ-CV-07) is resolved, partially or otherwise.
- That `distortPointCV` is invertible on any **open, physically meaningful** domain — only
  a singleton-set instantiation was exhibited (§8); proving invertibility on a ball or
  other practically useful region is not attempted and would require new work comparable
  in scope to `InjectivityModel.lean`'s existing (conditional) results, adapted to
  `distortPointCV`'s raw-ℝ coefficient representation rather than `RadialCoefficients`.

## 8. Concrete nontrivial numeric instantiation

`Pipeline/InverseConjugacyExample.lean`. Calibration: `k1=1` (all other radial coefficients
`0`), `p1=1, p2=0` — a genuinely distorting, non-identity lens — `F=2`, `fx=fy=1`, `w=2,
ws=1, h=2, h_shader=1` (so `F=(w/ws)·fx=2`, shared across both axes), `cx=cy=0`
(`ΔPx=ΔPy=-1`). Point `ε₀=(1,0)`.

Hand-computed and kernel-verified (`norm_num`): `CVmap(1,0)=(2,1)`;
`ScreenScale 2 (1,0)=(2,0)`; `OTImap(2,0)=(4,2) = ScreenScale 2 (2,1)`. `hCVInv`
instantiated on `A={(1,0)}`, `B={(2,1)}` with the constant function `cv' = fun _ => (1,0)`
— a legitimate, non-vacuous witness (not the all-zero-coefficient identity map the task
explicitly disallowed) that the hypothesis is satisfiable, built and checked by the Lean
kernel, not merely asserted by hand. This demonstrates **logical non-vacuity on a
non-identity example**, not invertibility on any open or physically representative domain
— that stronger claim is explicitly not made (§7).

## 9. Mathematical novelty vs. formalization value

The abstract identity in `conjugate_invOn` (conjugation of a partial inverse under an
invertible coordinate change) is standard, elementary function theory — no claim of
mathematical novelty is made for it. The value of this slice is **formalization value, not
mathematical novelty**: before this work, this repository had (a) no named function for the
OpenTrackIO-side forward map at all, (b) no y-component result for the corrected-scaling
model, (c) no statement anywhere connecting the proved forward conjugacy to any notion of
an inverse, and (d) consequently no honest, explicit record of exactly which hypothesis
(`distortPointCV`'s invertibility on some set) stands between the existing forward work and
a native-direction interoperability claim. This slice closes (a)–(c) and makes (d) visible
as a named, citable, undischarged hypothesis rather than an implicit gap. It does not
reduce the remaining distance to resolving SQ-CV-07 in a mathematical sense (that distance
is set by the impossibility result in
`audit/DISTORTION_DIRECTION_INTEROPERABILITY.md` §7, unaffected by this work) — it makes
the shape of that remaining distance precise and checkable.

---

## Summary: what was proved, what was not

**Proved**: a genuine, kernel-checked, two-dimensional forward conjugacy between the
corrected OpenCV and OpenTrackIO distortion maps; a general, standard, correctly-scoped
abstract fact about conjugating partial inverses under a bijection; the specialization of
that fact to the real maps in this repository, conditional on an explicit, honestly-flagged
hypothesis; and a concrete, non-trivial numeric witness that the hypothesis is satisfiable
at all.

**Not proved**: that `distortPointCV` is invertible on any practically meaningful domain;
that this inverse relates in any way to OpenLensIO's native undistortion function; that any
finite inverse-coefficient set exists (it provably does not, in general); that any real
implementation computes any of this correctly; or that SQ-CV-07 is resolved.
