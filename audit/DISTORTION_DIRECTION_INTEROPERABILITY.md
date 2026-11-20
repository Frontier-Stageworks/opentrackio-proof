# SQ-CV-07: Adversarial Investigation of OpenCV/OpenTrackIO Forward–Inverse Interoperability

**Scope.** Whether the corrected OpenCV→OpenTrackIO coefficient conversion
(`q=p/F`, `audit/ADVERSARIAL_LEAN_AUDIT.md` §4.1) provides actual interoperability with
OpenLensIO's *native* distortion semantics, or only establishes equality between two
same-direction mathematical models. No Lean files were modified, no new theorems were
written, and no existing P0/P1 audit, LAPS report, or specification-question status was
changed during this investigation — this document stands alone and is additive.

**Posture.** Adversarial. The repository's existing Lean proofs are not treated as
evidence for any claim about real-world interoperability; every claim below is either
traced to a primary source (the two PDFs, the JSON schema, or an external, independently
verified implementation) or explicitly marked as an inference or an open question.

---

## 1. Executive verdict

**SQ-CV-07 is not resolved by this investigation, and should not be closed by any single
theorem candidate identified here.** The strongest finding is a *negative* one, established
independently of this repository's Lean code: no finite-degree polynomial, and no rational
function of any degree, can be an *exact* inverse of a nontrivial Brown-Conrady map within
the same function family — proved here by an elementary degree-counting argument for the
polynomial case (§7, Test A) and, separately, a rigorous extension to rational functions
via degree-multiplicativity of rational-map composition (§7, "Test A, extended"), which
applies without qualification to the realistic multi-coefficient radial model. (An earlier
draft of this document additionally invoked the Abel–Ruffini theorem to claim no closed
form exists *at all*, even via radicals; that specific claim required a Galois-group
computation this investigation did not perform and has been withdrawn — see the correction
in §7, Test D. It is not needed: the rational-function result above is what this
repository's interoperability question actually depends on.) This means the premise of
"find an exact Brown-Conrady-shaped rational inverse-coefficient formula" is unsound in
general; the mathematically honest paths to native D→U interoperability remain numerical
inversion (which OpenLensIO's own spec already prescribes, Eq.11) or an independently-
fitted native coefficient set — understood as a calibrated *approximation*, not a proven
exact inverse (§7, Test B correction) — which the JSON schema's array-of-`Distortion`-
objects structure already accommodates without requiring any inversion at all (§4).

Separately, and more narrowly: proposition **A** (forward mathematical equivalence,
`opencv_openlensio_full_pipeline_pixel_corrected`) is established mathematically.
Proposition **B** (that a sample storing the converted coefficients with an explicit
`model="Brown-Conrady U-D"` tag correctly represents that forward operation per the
written schema) is established normatively, conditional on two explicit, separately-
checkable assumptions (§5.2). Proposition **C** (that a native-undistortion consumer can
correctly recover undistorted coordinates from such a sample) is **not** established, is
**not** implied by A or B alone, and — per the negative result above — cannot in general
be established by an *exact* coefficient-level theorem; it requires either a numerical-
approximation theorem (not yet proved for the real 6-coefficient rational model, only for
a simplified polynomial model, §8) or evidence that producers supply a separate native
D→U coefficient set directly (an operational, not mathematical, question — §6).

The single most valuable next step identified is **not** a new Lean theorem but a
**scoping decision**: whether this repository wants to pursue the expensive rational-model
numerical-inversion formalization (Candidate 3, §9) at all, given that the schema already
offers a zero-inversion resolution path (dual-direction storage) that this repository has
not yet investigated as a *normative* question. If a new theorem is prioritized, it should
be **Candidate 2** (general inverse-conjugacy, §9) — not because it resolves SQ-CV-07, but
because it is the cheapest genuinely new result that correctly *states* (without yet
discharging) what native-direction interoperability would require, closing the gap between
"same-direction conjugacy is proved" and "nothing about the inverse direction has even been
stated" that currently exists in this repository.

---

## 2. Primary-source equation and schema references

| Object | Primary source | Exact reference |
|---|---|---|
| OpenCV forward Brown-Conrady map | independently known (OpenCV `calib3d` documentation, cited in the conversion paper) | `docs/OpenCV_to_OpenTrackIO.pdf` p.1 |
| Conversion paper's coordinate identities (`ε'_u=F·x'`, `ε'_d=F·x''`) | SMPTE RIS conversion paper | `docs/OpenCV_to_OpenTrackIO.pdf` p.2 |
| Conversion paper's radial/tangential coefficient derivation | SMPTE RIS conversion paper | `docs/OpenCV_to_OpenTrackIO.pdf` p.2-3 |
| OpenLensIO native undistortion function `U` | OpenLensIO base spec | `docs/OpenLensIO_v1-0-1.pdf` §4.1, Eq.(16)-(17) |
| Statement that `U⁻¹` ("formerly named D") has no closed form | OpenLensIO base spec | `docs/OpenLensIO_v1-0-1.pdf` §2, Eq.(5), Eq.(11) ("solved using numerical iterative methods") |
| `ε'_u = F·[x,y]_u` coordinate identity (authoritative, not the conversion paper's restatement) | OpenLensIO base spec | `docs/OpenLensIO_v1-0-1.pdf` §3, Eq.(9) |
| Overscan equation asymmetry (independently confirmed, SQ-OL-02) | OpenLensIO base spec | `docs/OpenLensIO_v1-0-1.pdf` §2.1 Eq.(8) vs §3.1 Eq.(15) |
| `lens.distortion[].model` field: free string, no enum, `minLength:1, maxLength:1023` | OpenTrackIO JSON schema | `ris-osvp-metadata-camdkit/src/test/resources/classic/subschemas/lens.json:16-19` |
| Schema description: default `"Brown-Conrady D-U"` when absent; typo ("undistorted to undistorted") preserved verbatim in the normative text | OpenTrackIO JSON schema | `ris-osvp-metadata-camdkit/src/test/resources/classic/subschemas/lens.json:11` |
| `distortion` is an **array** of `{model, overscan, radial, tangential}` objects; only `radial` is `required` | OpenTrackIO JSON schema | `ris-osvp-metadata-camdkit/src/test/resources/classic/subschemas/lens.json:10-39` |
| This repository's parser decode of `model` (string passthrough, default on absence, never interpreted downstream) | this repository | `opentrackio_parser/LensModel.lean:7,68-73`, `opentrackio_parser/LensDecoder.lean:150,167-168` |
| Confirmation that `.model`/`"Brown-Conrady"` is never pattern-matched or branched on outside the decoder/encoder roundtrip | this repository | grep evidence, §4 below |

All PDF page/equation numbers above were read directly from the documents for this
investigation (continuing from the prior pass's full read of both), not taken from the
repository's citations of them.

---

## 3. Phase 1 — Normative model-direction matrix

Reconstructed independently from the two PDFs and the schema, not from the repository's
summary of them.

| Object | Input space/units | Output space/units | Direction | Structure | Coefficients | Domain restriction | Evaluable how |
|---|---|---|---|---|---|---|---|
| OpenCV forward map | normalized, dimensionless `(x',y')` | normalized, dimensionless `(x'',y'')` | U→D (undistorted in, distorted out) | rational (numerator/denominator degree ≤6 in `r²`) radial + additive quadratic tangential | `k1..k6` (OpenCV convention: `k1,k2,k3`=numerator, `k4,k5,k6`=denominator), `p1,p2` | denominator `1+k4r²+k5r⁴+k6r⁶≠0` (unstated in OpenCV docs; this repo's `hden`, free hypothesis) | direct evaluation (closed-form, no iteration) |
| Converted OTI forward model (conversion paper's "distortion function," `l,q`) | screen-space mm, `ε'_u=F·(x',y')` | screen-space mm, `ε'_d=F·(x'',y'')` | U→D | same shape as OpenCV's, same shape as OpenLensIO's Eq.(16) applied to the undistorted argument | `l1..l6` (same role as OpenCV `k1..k6`, different numeric values), `q1,q2` | same denominator condition, rescaled by `F` | direct evaluation (closed form) — this is a *same-shape* approximation to `U⁻¹`, **not** `U⁻¹` itself (no closed form for that exists, see below) |
| OpenLensIO native `U` | distorted screen coords, mm, `ε_d` (or `ε_d-ΔC-ΔP` per Eq.4) | undistorted screen coords, mm, `ε_u` | **D→U** | rational radial (Eq.17) + additive quadratic tangential (Eq.16) | native `k1..k6` (OTI alternating convention, §4.1), native `p1,p2`, units `mm⁻ⁿ⁻¹`/`mm⁻ⁿ`/`mm⁻²` respectively | none stated (SQ-OL-01, open) | direct evaluation (closed form) — `U` itself is directly evaluable; it is `U`'s *inverse* that is not |
| `U⁻¹` ("the distortion function, formerly named D") | undistorted screen coords | distorted screen coords | U→D | **no closed form in general** | none (not a fixed finite coefficient set — see §7) | — | **numerical iteration only** (Eq.5, Eq.11, stated explicitly in the spec) |
| `"Brown-Conrady U-D"` (schema string) | per schema description | per schema description | undistorted→distorted (the description's own text says "undistorted to undistorted," almost certainly a typo for "distorted" — `lens.json:11`) | — | the sample's `radial`/`tangential` arrays, interpreted as coefficients of *this* direction | — | implied: direct evaluation, same shape as `U` but applied U→D |
| `"Brown-Conrady D-U"` (schema string, **and the default**) | distorted screen coords | undistorted screen coords | distorted→undistorted | — | the sample's `radial`/`tangential` arrays, interpreted as `U`'s own native coefficients | — | implied: `U` itself, direct evaluation |
| Default when `model` absent | — | — | **D→U** (`"Brown-Conrady D-U"`) | — | — | — | — |

**Does the schema explicitly support storing forward coefficients without converting them
to an inverse-model set?** Yes, **syntactically**: `model` is an unconstrained string
(`minLength:1,maxLength:1023`, no `enum`), and `radial`/`tangential` are plain number
arrays with no cross-field validation against `model`, focal length, or sensor dimensions.
A producer can set `model="Brown-Conrady U-D"` and store any numbers at all — including,
incorrectly, raw unconverted OpenCV `k,p` with no `F`-rescaling applied — and the schema
will accept it. **Semantically**, the schema's prose (not enforceable by the schema
itself) ties `"Brown-Conrady U-D"` to "mapping undistorted to [distorted] coordinates,"
which is a direction label, not a coefficient-correctness check. **This is a real gap
between what the schema permits and what the specification means**: syntactic validity
(a well-formed `model` string plus well-formed number arrays) is not sufficient evidence
that the stored numbers actually satisfy the forward-conjugacy relationship this
repository's theorem proves; that is a property of how the *producer* computed the
numbers, which the schema cannot check and does not attempt to.

A second structural point, independently useful for §5/§6: **`distortion` is a JSON
array**, not a single object (`lens.json:10-39`). The schema already anticipates a sample
carrying *more than one* `Distortion` entry for the same lens state. This means a producer
could, in principle, supply **both** a natively-fitted `"Brown-Conrady D-U"` entry (from a
real D→U calibration) **and** a converted `"Brown-Conrady U-D"` entry (from this
repository's conversion) in the same sample — letting any consumer pick whichever
direction it needs directly, with no inversion required by anyone. Whether any producer
actually does this is an operational question (§6), not a schema limitation.

---

## 4. Current Lean coverage of the three model objects (evidence, not inference)

Three distinct mathematical objects exist in this repository's Lean code, and they are
**not connected to each other or to the parser's `model` field** by any current theorem:

1. `distortXCV`/`distortYCV`/`distortPointCV` — OpenCV's forward map, named `def`s
   (`opencv_opentrackio_proofs/Pipeline/OpenCVModel.lean:41,59,77`).
2. The OTI-side forward map using `l,q` — **not a named `def` anywhere**; it exists only
   as a fully-inlined real-number expression inside the statements of
   `opencv_openlensio_full_pipeline_pixel_iff` (`Pipeline/PixelIff.lean:42-57`) and
   `opencv_openlensio_full_pipeline_pixel_corrected` (`Pipeline/PixelIffCorrected.lean:83-100`).
   Confirmed by `grep -n "^def \|^noncomputable def " opencv_opentrackio_proofs/Pipeline/*.lean opencv_opentrackio_proofs/*.lean`
   — the only matches are the three `OpenCVModel.lean` definitions above.
3. `undistortX`/`undistortY`/`undistortPoint` — OpenLensIO's **native** `U` (D→U), named
   `def`s (`openlensio_semantics/DistortionModel.lean:26,38,51`), operating on
   `RadialCoefficients`/`TangentialCoefficients` (`openlensio_semantics/LensSemantics.lean:35-55`,
   OpenLensIO's own alternating-convention `k,p`, mm units — confirmed distinct from
   `DistortionConversion.lean`'s OpenCV-convention raw-`ℝ` parameters by
   `docs/specification-questions.md` SQ-CV-03, independently re-confirmed by reading both
   files side by side).

The parser's `Distortion.model : String` field (`opentrackio_parser/LensModel.lean:68-73`,
decoded at `opentrackio_parser/LensDecoder.lean:150-169`) is read, defaulted to
`"Brown-Conrady D-U"` on absence, and re-encoded verbatim
(`opentrackio_parser/LensSubEncoders.lean:42,102`) — confirmed by
`grep -rn "\.model\b\|Brown-Conrady" --include=*.lean . --exclude-dir=.lake` that this
string is **never pattern-matched or branched on anywhere outside the decode/encode
roundtrip**: no Lean declaration anywhere connects a decoded `model` value to a choice
between `undistortPoint` (object 3) and the pipeline theorems' inline OTI forward map
(object 2). This is the precise, verifiable sense in which "the parser handles the
default correctly for decode purposes" (as `docs/specification-questions.md` SQ-CV-07
already states) while the *semantic* meaning of that string is formalized nowhere.

---

## 5. Phase 2 — Propositions A, B, C

### 5.1 Proposition A — forward mathematical equivalence

> The corrected coefficients define the same forward distortion map as OpenCV, expressed
> in the corresponding scaled coordinate system.

- **Already established**: yes — `opencv_openlensio_full_pipeline_pixel_corrected`
  (`Pipeline/PixelIffCorrected.lean:71-132`), proved over all reals satisfying the stated
  hypotheses, depending only on `propext, Classical.choice, Quot.sound`
  (`audit/ADVERSARIAL_LEAN_AUDIT.md` §2.4). Independently re-confirmed in this
  investigation's own terms (§2-3 above) without reference to the Lean proof.
- **Follows from normative definitions**: yes, under the reading of the conversion paper's
  stated coordinate identities established in the prior adversarial pass
  (`audit/ADVERSARIAL_LEAN_AUDIT.md` §4.1.2) and re-confirmed here against the base
  OpenLensIO spec's Eq.(9), Eq.(16)-(17).
- **Requires a new theorem**: no.
- **Requires implementation evidence**: no — this is a pure mathematical identity.
- **Remains ambiguous**: no, within its own stated scope (same-direction, U→D,
  coordinate-conjugate comparison). **Verdict: established mathematically.**

### 5.2 Proposition B — OpenTrackIO representation correctness

> An OpenTrackIO sample that stores those coefficients and explicitly sets
> `model = "Brown-Conrady U-D"` correctly represents that forward distortion operation
> according to the specification.

**Does A imply B?** Yes, **under exactly two explicit semantic assumptions**, neither of
which is proved or disproved by any Lean theorem in this repository:

1. **Direction-string semantics assumption**: that `"Brown-Conrady U-D"` means precisely
   "evaluate the Eq.(16)-shaped formula in the undistorted-input/distorted-output
   direction, using the stored `radial`/`tangential` arrays as that formula's own
   coefficients" — i.e. exactly the role this repository's conversion paper assigns to
   `l,q`. This is the single most natural reading of the schema's description text
   (`lens.json:11`, modulo its own typo) and of the conversion paper's framing of `l,q`
   as "the distortion function... the inverse of U" (`OpenCV_to_OpenTrackIO.pdf` p.1), but
   it is a reading, not something the schema enforces or the paper states in so many
   words.
2. **Reconstructible-scale assumption**: that a consumer reading the sample can recover
   the *same* `F, w, ws` values the producer used when computing the conversion — i.e.
   that the scale relationship `ε'_u=F·x'` a consumer would use to interpret the stored
   coefficients matches the one the producer used to derive them. This was **not**
   independently re-verified in this pass (it would require a full audit of how
   `focalLength`, sensor-dimension, and shader-resolution fields are transmitted and
   whether `F` is uniquely reconstructible from them — out of scope here); it is reported
   as an **open assumption**, not a checked fact.

Given both assumptions, A⟹B is a direct corollary: the pixel-level conjugacy A proves
is exactly what "correctly represents the forward operation" should mean. **Verdict:
established normatively, conditional on (1) and (2) above being explicitly recorded as
assumptions** — this is a different, weaker claim than "B is established," and should not
be stated without the conditional.

- **Requires a new theorem**: arguably yes — a *statement-level* theorem connecting the
  Lean `Prop` "`A` holds" to the Lean `Prop` "`model = "Brown-Conrady U-D"` is the correct
  tag for this sample" would make assumption (1) explicit and checkable rather than only
  asserted in prose (Candidate 1, §9).
- **Requires implementation evidence**: for assumption (2), yes, if it is to become more
  than an open assumption.

### 5.3 Proposition C — native undistortion correctness

> A consumer that requires distorted-to-undistorted coordinates can correctly obtain them
> from the stored representation.

**Does B imply C?** **Only when the consumer correctly computes the inverse of the stored
forward operation.** This is not automatic, and is the crux of SQ-CV-07:

- If B holds (the sample correctly represents a U→D forward operation), a consumer
  needing D→U coordinates must apply the **inverse** of that stored map. Per §7 below,
  that inverse has **no general closed form** — it must be computed numerically (Newton's
  method, fixed-point iteration, or a Banach-type contraction argument), exactly as
  OpenLensIO's own spec prescribes for `U⁻¹` (Eq.11).
- A consumer that instead *reinterprets* the stored `l,q` as if they were `U`'s own native
  `k,p` (i.e., feeds a distorted point directly into Eq.(16)'s formula shape using the
  transmitted numbers) is **not** computing an inverse at all — it is evaluating an
  unrelated function. §7 Test B constructs an exact-rational-arithmetic example where this
  produces a result wrong by a factor of 33 relative to the true undistorted coordinate.
- **Alternative path to C that requires no inversion at all**: if the schema's
  array-of-`Distortion`-objects structure (§3) is used to transmit a *separately-fitted*
  native D→U coefficient set directly (rather than deriving D→U from the U→D conversion),
  C can be satisfied exactly, with no approximation and no numerical iteration — this is
  "evaluating a separately fitted inverse polynomial" in Test B's taxonomy, a different
  operation from both of the above. Whether any real producer does this is an operational
  question (§6), reported as unverified, not as false.

**Is an explicit U-D declaration sufficient for standards-compliant data interchange even
when some real consumers only support D-U?** Yes — this is explicitly **not** a
mathematical failure of the format. A specification that defines two directions and lets
a producer declare which one it is using is standards-compliant regardless of whether a
particular consumer implementation has chosen to support only one direction. A consumer
that ignores the declared `model` value and always treats incoming coefficients as D-U
(for instance, by applying `U`'s formula regardless of the tag) is a **consumer defect**,
not a format defect — this distinction matters for how any future finding here should be
phrased, and is maintained throughout this document.

- **Already established**: nothing beyond "B does not imply C without an inversion step."
- **Follows from normative definitions**: that inversion, if attempted exactly, is
  impossible in general (§7) — this is new to this investigation, not previously stated
  in the repository's artifacts.
- **Requires a new theorem**: yes, if C is to be established at all for the rational
  model — and only as an *approximation* theorem (Candidate 3), since an exact one cannot
  exist in general (§7).
- **Requires implementation evidence**: yes — whether any real consumer performs numerical
  inversion, reuses coefficients across directions incorrectly, or receives a
  separately-fitted native set (§6).
- **Remains ambiguous**: whether real producers populate a native D→U entry at all; this
  investigation could not determine this one way or the other (§6).
  **Verdict: mathematically compatible (an approximate/numerical path to C exists in
  principle) but operationally unverified, and incompatible with an *exact* finite-
  coefficient-reuse interpretation (§7).**

---

## 6. Phase 4 — Operational implementation survey

Searched beyond the two libraries the prior adversarial pass inspected
(`ris-osvp-metadata-camdkit`, `opentrackio-cpp`, both confirmed to be schema/data-model
libraries only, no distortion evaluation). This pass additionally searched the web for
implementations that *evaluate* (not merely store) a Brown-Conrady distortion or
undistortion function in connection with OpenTrackIO/OpenLensIO.

| Implementation | Repository/source | What was found | Tested or inspected | What cannot be concluded |
|---|---|---|---|---|
| Epic Games `LiveLinkOpenTrackIO` plugin | Unreal Engine (closed-source core; public API reference at `dev.epicgames.com`) | Confirmed to exist as a real, shipped, actively-documented plugin. Exposes Blueprint nodes `MakeLiveLinkOpenTrackIOLens`, `BreakLiveLinkOpenTrackIOLensDistortionCoeff` with fields **Model, Radial, Tangential, Overscan, Custom** — i.e. it parses the `distortion[].model` string directly out of the schema into engine-accessible data, not just the coefficient arrays. | **Inspected via public documentation/search snippets only** (`dev.epicgames.com` API pages are JavaScript-rendered and returned empty "Table of Contents" shells to automated fetch; could not retrieve full page text). **Not tested.** | Whether Unreal's rendering pipeline actually branches its distortion evaluation on the parsed `Model` string value, or passes the raw coefficient arrays through to UE's own `FSphericalDistortionParameters` (a separately-named struct using OpenCV-style `K1,K2,P1,P2,K3` naming, per `dev.epicgames.com/.../FSphericalDistortionParameters`) regardless of the declared direction. This is the single most decision-relevant fact for SQ-CV-07 and it could not be determined from public sources in this pass. |
| Unreal Engine `CameraCalibrationCore` / `OpenCVLensDistortion` plugins | Unreal Engine (closed-source) | Confirmed to exist; documentation states the calibration tool can **either calibrate its own coefficients from checkerboard images (OpenCV-based) or ingest externally-streamed lens data from third-party tracking vendors** (`dev.epicgames.com/.../camera-lens-calibration-overview`, per search-engine-summarized content). | Inspected via search summary only; direct page fetch returned no renderable content. **Not tested.** | Whether "externally-streamed lens data" ingestion path specifically parses OpenTrackIO's `distortion[].model`/`l,q` representation, or only vendor-specific proprietary formats; whether it is the forward or inverse direction that gets applied to the render. |
| `ris-osvp-metadata-camdkit` (Python) | this machine, `~/github/ris-osvp-metadata-camdkit` | Pure schema/data-model library; `lens_types.py` stores `tangential: tuple[float,...]` as opaque numbers with no model-aware computation (confirmed by direct source inspection, prior pass) | **Tested by direct source inspection** (full read of `lens_types.py`, grep across `src/main/python`) | Confirmed **not** a distortion-evaluating implementation; this is a settled, not merely absent, finding. |
| `opentrackio-cpp` | this machine, `~/github/opentrackio-cpp` | Same: pure data-model library, `distortion: Distortion` struct storing `radial`/`tangential` vectors, no evaluation code | **Tested by direct source inspection** | Same as above — confirmed, not merely unfound. |

**Explicit statement per the task's restriction**: the absence of an evaluating
implementation in the two locally-available reference repositories is **not** evidence
that no such implementation exists anywhere. A real, named, production implementation
(Epic's `LiveLinkOpenTrackIO` plus `CameraCalibrationCore`) was identified via web search
and is almost certainly the dominant real-world consumer of OpenTrackIO lens data in
virtual-production pipelines today — but its internal dispatch logic is closed-source and
could not be verified from publicly available documentation in this pass. **This question
is reported as operationally unverified, not resolved in either direction.** A thorough
resolution would require either Epic Games documentation/source access this investigation
does not have, or direct empirical testing (feeding a known-direction sample into the
plugin and observing rendered output) — not performed here.

**Conformance vs. ecosystem behavior**: nothing found in this pass contradicts the written
specification's permissiveness (§3's model-direction matrix); what remains unknown is
purely an ecosystem-behavior question, not a specification-conformance one.

---

## 7. Phase 3 — Hostile examination of forward/inverse coefficient reuse

Claim under test: **"The corrected OpenCV forward coefficients can be used unchanged as
native OpenLensIO D-U coefficients."** This section tries to disprove it, beginning with
the simplest possible model.

### Test A — polynomial inverse obstruction (elementary, rigorous, one-dimensional)

Let `D(x) = x + a·x³`, `a≠0`. Suppose some polynomial `U` (any finite degree `n≥0`)
satisfies `U(D(x)) = x` as a polynomial identity (equal for all `x`, not just numerically
at sample points).

- `D` has degree 3 (leading term `a·x³`, `a≠0`).
- For nonconstant polynomials over a field, `deg(U∘D) = deg(U)·deg(D)` (composition
  multiplies degrees — the leading coefficient of the composition is a nonzero multiple
  of `a^{deg U}` times `U`'s leading coefficient, so no degree-cancellation can occur).
- If `n≥1`: `deg(U∘D) = 3n ≥ 3`, but `deg(x) = 1`. `3n=1` has no solution in positive
  integers. **Contradiction.**
- If `n=0` (`U` constant): `U∘D` is constant, which cannot equal the non-constant
  polynomial `x`. **Contradiction.**

**Conclusion: no finite-degree polynomial `U` satisfies `U(D(x))=x` identically, for any
`a≠0`.** This is a complete, elementary proof requiring nothing beyond polynomial-degree
arithmetic.

**What this does and does not imply for two-dimensional Brown-Conrady distortion:**

- It **does** imply that the simplest possible building block of the radial term — a
  single nonzero numerator coefficient acting alone (`r ↦ r + k1·r³`, exactly this `D`
  with `a=k1`) — already has no exact polynomial inverse. Since the full Brown-Conrady
  radial term is a rational function built from sums of such terms (plus a denominator),
  this rules out the simplest possible escape route (a lucky cancellation making the
  *whole* radial map simple to invert) in the most elementary nonzero case.
- It does **not**, by itself, prove anything about the full rational (numerator/denominator)
  model or about two-dimensional maps (where radial and tangential terms interact). It
  also does not, *by the polynomial-degree argument alone*, cover *rational* (as opposed
  to strictly polynomial) candidate inverses — a separate argument, using the degree of a
  rational map rather than a polynomial, is needed and is given immediately below
  (§7, "Test A, extended") — this is **not** the same statement as the plain polynomial
  case and is presented as its own, separately justified result, not an immediate corollary.
- **Local numerical invertibility coexists with this result without contradiction**
  because they are different kinds of claims. The Inverse Function Theorem gives a
  *local*, generally non-polynomial, non-rational function (often only a convergent power
  series, or a function evaluable only by root-finding) near any point with nonsingular
  Jacobian. "No exact finite-degree algebraic inverse exists in the same function family"
  (an algebraic/degree-theoretic fact) and "a local inverse function exists and is unique
  near this point" (an analytic fact, via IFT or a contraction argument) are not in
  tension — the second does not produce a formula of the first kind, and the first does
  not deny the second.

### Test A, extended — no exact RATIONAL FUNCTION inverse either (one dimension)

The task brief specifically asked for this to be strengthened to rational functions, not
only polynomials, and to have any extension beyond the simple cubic case justified
precisely rather than asserted. This is done here using the degree of a rational map,
not Galois theory or Abel–Ruffini (that theorem is explicitly NOT invoked for this
claim — see the correction to the earlier draft's Test D below).

**Fact used (standard, not re-derived from scratch here, but stated precisely so the
reduction is checkable): for nonconstant rational functions `φ, ψ` over a field, writing
each in lowest terms as a ratio of coprime polynomials, the degree of a rational function
`deg(φ) := max(deg(numerator), deg(denominator))` is multiplicative under composition:
`deg(ψ∘φ) = deg(ψ)·deg(φ)`.** This is the function-field-extension-degree fact
`[K(x) : K(ψ(φ(x)))] = [K(x):K(φ(x))]·[K(φ(x)):K(ψ(φ(x)))] = deg(φ)·deg(ψ)`, valid
whenever `φ` is nonconstant (so `φ(x)` is transcendental over the base field and the tower
law applies cleanly) — it holds unconditionally for nonconstant `φ, ψ`, with no genericity
or non-degeneracy caveat needed for the multiplicativity itself (unlike the Abel–Ruffini
application removed below, which does carry such a caveat).

**Application to `f(x) = x + a·x³`, `a≠0`.** As a rational function, `f = (x+ax³)/1`, so
`deg(f) = max(3, 0) = 3`. Suppose a nonconstant rational function `g` satisfies
`g(f(x)) = x` identically (a genuine rational-function identity, not merely agreement at
sample points). Then `deg(g∘f) = deg(g)·deg(f) = 3·deg(g)`. But `g∘f` equals the identity
function `x`, which has degree `max(1,0) = 1`. So `3·deg(g) = 1`, which has no solution
with `deg(g)` a positive integer. If `g` is constant, `g∘f` is constant, which cannot
equal the nonconstant function `x`. **Contradiction either way: no rational function `g`
satisfies `g(f(x))=x` identically, for any `a≠0`.** This is strictly stronger than the
polynomial-only result above (it rules out *all* rational candidates, not only polynomial
ones), proved by the same style of elementary degree-counting, now using the degree of a
rational map rather than a plain polynomial degree.

**Extending to the actual (multi-coefficient, rational) Brown-Conrady radial map — stated
precisely, with the reduction spelled out, not asserted.** Restrict attention to the pure
radial map in one real variable `r ≥ 0` (tangential terms and the second dimension are not
addressed by this argument — see the scope note below): `h(r) = r · N(r²)/D(r²)`, where
`N(u) = 1+k1u+k2u²+k3u³` and `D(u) = 1+k4u+k5u²+k6u³`. As a rational function of `r`,
`h(r) = [r·N(r²)] / D(r²)`. Write `n := deg_r(r·N(r²))` and `d := deg_r(D(r²))`
(so `d ∈ {0,2,4,6}` depending on which of `k4,k5,k6` are the highest nonzero one, and
similarly `n ∈ {1,3,5,7}`). **Precise, checkable condition for the argument to apply**:
whenever `h`, in lowest terms, has `deg(h) = max(n,d) > 1` — i.e. whenever the radial map
is not already degree ≤ 1 after cancellation (the only way `deg(h) ≤ 1` is if the
coefficients are such that `h` collapses to an affine function of `r`, e.g. the all-zero
case `h(r)=r`, or another coefficient choice producing an exact cancellation down to
degree 1 in lowest terms — not separately characterized here, but a measure-zero/special
condition on the coefficients, not the generic case) — the same degree-multiplicativity
argument gives: no rational function `g` satisfies `g(h(r))=r` identically, since
`deg(g)·deg(h) = 1` would again require `deg(g) = 1/deg(h) ∉ ℤ_{>0}` whenever
`deg(h) > 1`. **This is the result that actually matters for this repository's
interoperability question**: it directly rules out an exact rational-function (not merely
polynomial) inverse for the radial part of the real, multi-coefficient OpenLensIO/OpenCV
Brown-Conrady model, in every non-degenerate case, via a fully elementary and rigorously
applicable argument — no Galois-theoretic machinery, and no unverified genericity
assumption about a Galois group, is needed to reach this conclusion.

**Scope of this extension — what it does and does not cover**, stated explicitly per the
task's caution against over-generalizing: (a) it covers the **pure radial, one-dimensional
reduction** of the model only — it says nothing by itself about the full two-dimensional
map once tangential terms are included, where radial and tangential terms interact and the
map is not a rational function of a single real variable in the same simple sense; (b) it
establishes non-existence of an exact inverse *within the rational-function class*, not
within any larger class (radicals, elementary functions, or other special functions) — see
the corrected Test D below for why this document does not extend the claim further; (c)
the degenerate/special coefficient cases where `deg(h) ≤ 1` are noted as exceptions, not
separately enumerated or ruled out here — the argument applies to the generic, truly
distorting case, which is the physically relevant one (a lens with `deg(h) ≤ 1` is, in
the cases checked, barely distorting at all).

### Test B — wrong-direction coefficient consumption (exact rational arithmetic)

Construction: pure-tangential lens, OpenCV `p1=1`, all other OpenCV coefficients `0`.
Normalized undistorted point `(x',y')=(1,1)`.

1. **OpenCV forward distortion** (direct evaluation of the formula in §2): radial factor
   `R=1` (all `k`'s zero); `x''=1·1+2·1·1·1=3`; `y''=1·1+1·(1²+1²+2·1²)=1+4=5`. Distorted
   point `(x'',y'')=(3,5)` exactly (all integers, exact rational arithmetic throughout).
2. **Convert via the corrected (dimensionally-consistent) formula** with `F=2`:
   `q1=p1/F=1/2`, `q2=0`, `l`'s `=0`. The resulting OTI-side forward map, applied at
   `ε'_u=F·(x',y')=(2,2)` (`r_u²=8`), gives: `ε'_{d,x}=1·2+2·(1/2)·2·2+0=2+4=6`;
   `ε'_{d,y}=1·2+(1/2)·(8+2·4)+0=2+(1/2)·16=2+8=10`. Result `(6,10)`, exactly equal to
   `F·(x'',y'')=(6,10)` — confirming proposition A (forward conjugacy) holds exactly for
   this example, as already established in §5.1.
3. **Wrong-direction misuse**: a consumer receives the sample's stored coefficients
   (`l=0,q1=1/2,q2=0`) and, because `model` is absent or mis-set to the default
   `"Brown-Conrady D-U"`, treats them as **native `U`-coefficients** (plugs `l→k`-role,
   `q→p`-role into Eq.(16) directly) and evaluates `U` at the transmitted *distorted*
   screen point `ε_d=(6,10)` (`r²=36+100=136`, `R=1`): `U(ε_d)_x = 1·6+2·(1/2)·6·10+0 =
   6+60 = 66`.
4. **Compare to the true undistorted screen coordinate**, which is `ε'_u=(2,2)` (step 2).
   The wrong-direction evaluation gives `66`, versus the true value `2` — **exact
   rational round-trip error of `64`**, a 33-fold overshoot, not a small numerical
   discrepancy. (All quantities above are exact rationals/integers; no floating point was
   used.)

**The three distinct operations, kept separate as required:**

- *Applying the same forward polynomial twice* (`D(D(ε))`): not performed by any real
  consumer scenario here; included only to note it is a different, unrelated operation
  from either of the below and not a candidate for recovering an undistorted point.
- *Evaluating a separately-fitted inverse polynomial*: this is what OpenLensIO's **native**
  `U`, with its **own independently-calibrated** `k,p` (obtained by fitting a real D→U
  calibration directly, not by converting OpenCV's forward coefficients), is *intended* to
  approximate. **Correction, per adversarial review of the earlier draft of this
  document**: a separately-fitted native `k,p` set is not thereby established to be the
  *exact* functional inverse of anything — fitting is itself an approximation procedure
  (least-squares or similar, against measured calibration data), not a proof of exact
  inversion, and §7 Test A/"Test A, extended" above show an exact rational-function inverse
  of a nontrivial Brown-Conrady map generally does not exist for it to exactly equal in the
  first place. The correct, precisely-scoped claim is: a native, independently-fitted `k,p`
  is a *directly evaluable, independently-calibrated approximation* to the true (generally
  non-rational, non-closed-form) inverse — useful and intended for exactly this purpose,
  but not proved here (or anywhere in this repository) to be exact, and categorically
  different from both (i) reusing the *converted* `l,q` coefficients in the wrong role
  (step 3's error, demonstrably wrong by the counterexample above) and (ii) numerically
  inverting the actual forward function at evaluation time (the third bullet below). This
  repository's `undistortPoint` (`DistortionModel.lean:51`) correctly *evaluates* `U` given
  whatever native coefficients it is handed — that evaluation is not in question; what is
  corrected here is only the earlier draft's unsupported suggestion that a native,
  separately-fitted coefficient set is automatically the exact inverse of the converted
  `l,q` forward map, rather than an independent approximation to a different, generally
  non-closed-form target.
- *Numerically inverting the actual forward function*: applying Newton's method or a
  fixed-point/contraction iteration to the **actual** forward map built in step 2 (not to
  `U`) would recover `ε'_u=(2,2)` exactly (by construction, since that forward map was
  built to send `(2,2)↦(6,10)`) — this is the operation OpenLensIO's spec prescribes
  (Eq.11) and the operation this repository's `inverse_approximation/` module formalizes
  for a simplified model (§8). It is categorically different from step 3's error.

### Test C — conditions under which an inverse is valid

- **Local injectivity / IFT**: requires the Jacobian of the forward map to be nonsingular
  at the point of interest; gives local bijectivity onto a neighborhood of the image
  point, as part of the same theorem (not a separate "surjectivity" condition to check).
- **Sufficient contraction conditions**: this repository's `inverse_approximation/InverseApproximation.lean`
  uses `|t|·L θ R < 1` (a Banach/`ContractingWith` condition, stronger than bare IFT since
  it gives existence/uniqueness on an entire specified disk, not just a germ near one
  point) — `D_exists_unique_preimage` (`InverseApproximation.lean:596-642`).
- **Domain restrictions for rational denominators**: **not present anywhere in
  `InverseApproximation.lean`**, because that model has no denominator — confirmed by
  inspection: `Coeffs` (`InverseApproximation.lean:35-40`) has only `k1,k2,k3,p1,p2`,
  a pure polynomial field `Φ`. The actual OpenLensIO rational model's denominator-nonzero
  condition (`denominatorNonzero`, used throughout `openlensio_semantics/RadialPolynomial.lean`
  and `InjectivityModel.lean`) has **no corresponding Lipschitz/boundedness/domain-invariance
  analysis anywhere in this repository**.
- **Conditions ensuring an inverse iteration stays in its domain**: proved for the
  polynomial model (`inverse_step_maps_disk`, `InverseApproximation.lean:553-562`, a
  self-mapping/buffer condition); **no analogous result exists for the rational model**,
  where "staying in the domain" would additionally require the iteration to stay in a
  region where the denominator remains bounded away from zero, not merely inside a disk.

**What the repository already proves for the actual rational model, and what it does
not:**

| Property | Polynomial toy model (`inverse_approximation/`) | Actual 6-coefficient rational model (`openlensio_semantics/`) |
|---|---|---|
| Boundedness/Lipschitz bounds | ✅ `phi_bounded`, `phi_lipschitz` | ❌ none |
| Injectivity | ✅ `D_injective_on_disk` | ✅ partial — `undistortPoint_injective_pure_radial`/`_zero_tangential`/`_on_circle_tangential` (`InjectivityModel.lean:66-286`), each **conditional** on a caller-supplied hypothesis (`hScaleInj`, `hDet`), with `hScaleInj` constructively dischargeable under a sign-separation coefficient condition (`radialScale_hScaleInj`, `:426-453`) — **no unconditional global injectivity theorem exists for the rational model** |
| Existence of a true inverse | ✅ `D_exists_unique_preimage` | ❌ none |
| Approximation-error bound | ✅ `inverse_approx_error`, `inverse_approx_error_vs_preimage` | ❌ none |

**This investigation does not assume global invertibility from local invertibility
anywhere above** — the table above is deliberately split by exactly this distinction, and
the repository's own existing work is credited for maintaining the same discipline (no
theorem in `InjectivityModel.lean` claims unconditional global injectivity; each is
explicit about its caller-supplied or constructively-discharged hypothesis).

### Test D — are exact rational-model inverses ever possible?

**Correction to an earlier draft of this document.** A previous version of this section
invoked the Abel–Ruffini theorem to claim that the general multi-coefficient radial
inverse has "no closed-form expression at all, not even via radicals." **That claim is
withdrawn as unsupported.** Abel–Ruffini states that a *generic* degree-`n` (`n≥5`)
polynomial — one whose Galois group over the field generated by its own coefficients is
the full symmetric group `S_n` (or otherwise non-solvable) — has no root formula in
radicals. The equation obtained from the Brown-Conrady radial map (`r·N(r²)=r_out·D(r²)`,
a degree-≤7 polynomial equation in `r`) is **not** a generic degree-7 polynomial: it has a
restricted, sparse structure (only odd powers of `r` appear, since `N`, `D` are polynomials
in `r²`), and restricted polynomial families can have Galois groups strictly smaller than
`S_n` — some such families remain solvable by radicals even at degree ≥5 (for example,
polynomials of the form `x^n - c`, or other families with extra symmetry). **This document
did not compute, bound, or otherwise establish the Galois group of the specific family
`r·N(r²) - r_out·D(r²)` over the field generated by `k1,...,k6,r_out`**, and so citing
Abel–Ruffini to conclude radical-unsolvability for this family was not justified — doing so
correctly would require a separate, nontrivial algebraic argument (e.g. computing the
Galois group directly, or exhibiting it as a specialization of a known non-solvable family
in a way that provably preserves non-solvability) that this investigation has not carried
out. The claim is downgraded to **insufficient evidence** pending that argument, not
reinstated in a weaker form elsewhere in this document.

**What is established instead, with no such gap**, is the strictly more relevant and fully
rigorous result from "Test A, extended" above: no **rational function** (regardless of
degree) is an exact inverse of the non-degenerate Brown-Conrady radial map, via
degree-multiplicativity of rational-map composition — a classical, unconditionally-valid
fact requiring no genericity assumption about any Galois group. This is the correct
replacement for the withdrawn Abel–Ruffini claim, and it is actually the more directly
relevant question for this repository's purposes: the interoperability question at stake
(§5, Proposition C) is specifically whether an exact finite *Brown-Conrady-shaped rational*
inverse-coefficient set exists — which "Test A, extended" settles — not the broader and
separately-open question of whether some other closed form (radicals or otherwise) exists.

- **Trivial case**: all coefficients zero — `U=D=`identity, trivially self-inverse within
  the family (`brown_conrady_zero_identity`, `DistortionModel.lean:78-92`, already proved
  in this repository, independent of this investigation).
- **Single-nonzero-coefficient radial case** (`r↦r+k1r³`, i.e. Test A's `D` again): this
  specific cubic *is* solvable by radicals (Cardano's formula), giving an exact algebraic
  expression for the inverse as a function of the output radius — but that expression is
  **not** a polynomial or rational function, so it still does not produce "an exact inverse
  within the same Brown-Conrady rational-function family," only an exact closed-form
  expression in the strictly larger class of radical expressions. This one case does not
  generalize to the full multi-coefficient family — see the correction above.
- **General multi-coefficient radial case**: whether a closed-form (radical or otherwise)
  solution exists is genuinely **insufficient evidence** per this investigation — neither
  established nor ruled out here, pending a proper Galois-theoretic argument not attempted.
  What *is* established without qualification is "Test A, extended"'s rational-function
  non-existence result, which does not depend on this open question at all.

**Verdict on Test D**: a general exact finite rational-coefficient inverse-conversion rule
(a formula producing `U`'s native `k,p`, as a Brown-Conrady-shaped **rational function**,
from OpenCV's forward `k,p`, valid for all non-degenerate coefficient choices) is
**rigorously impossible**, established via "Test A, extended"'s degree-multiplicativity
argument — not merely unproved, and not dependent on Abel–Ruffini. Whether some *other*,
non-rational closed form (radicals, or a named special function) exists for the general
multi-coefficient case is **insufficient evidence** — genuinely open, not resolved in
either direction by this document, and should not be cited as settled by either the
withdrawn Abel–Ruffini argument or anything that replaces it above. Special, non-generic
coefficient choices (all-zero; the single-coefficient case solvable by radicals but outside
the rational-function family) remain exceptions that do not rescue a *general* rational
conversion rule, which is the claim this repository's interoperability question actually
turns on.

---

## 8. Phase 5 — Candidate theorems

### Candidate 1 — explicit forward-model interpretation

**Statement**: formalize, as a Lean `Prop`, the claim "a `Sample` whose `Lens.distortion`
entry has `model = "Brown-Conrady U-D"` and whose `radial`/`tangential` arrays were
produced by the corrected conversion from a given OpenCV calibration is semantically
equivalent (via `opencv_openlensio_full_pipeline_pixel_corrected`) to that OpenCV
calibration's forward map" — i.e. a bridge between the **parsed, typed** `Distortion`
value (`LensModel.lean:68-73`) and the **already-proved** mathematical fact (A, §5.1).

- **Existing declarations to reuse**: `opencv_openlensio_full_pipeline_pixel_corrected`
  (already does the hard mathematical work); `Distortion`, `decodeDistortion`
  (`LensModel.lean`, `LensDecoder.lean`) for the parsed representation.
- **Necessary hypotheses**: that the sample's `model` string is literally
  `"Brown-Conrady U-D"`; that the numeric arrays, once parsed from their raw-string
  representation, equal the `l,q` values the conversion formula produces from some given
  OpenCV `k,p,F`.
- **Mathematical strength**: essentially **none beyond what is already proved** — this
  candidate's "new" content is almost entirely the *plumbing* connecting a `String`
  equality and a `List`-to-coefficient decoding step to an already-proved real-number
  identity, not new mathematics.
- **Interoperability relevance**: addresses proposition B only (§5.2), and only assumption
  (1) of the two listed there — it would not touch assumption (2) (reconstructible scale)
  at all.
- **Main Lean obstacles**: none significant — this is a direct, mechanical composition of
  existing results.
- **Genuinely new or repackaging?** **Mostly repackaging.** The task instruction not to
  "propose a redundant theorem merely to increase theorem count" applies directly: the
  missing work here is a thin semantic-linkage lemma, not a new mathematical result. It
  would be worth doing as *documentation-as-code* (making assumption (1) of §5.2 checkable
  rather than asserted in prose) but should not be oversold as resolving anything about
  proposition C.

### Candidate 2 — inverse conjugacy

**STATUS UPDATE (post-dates the original Phase 5 analysis below): implemented.** See
`audit/INVERSE_CONJUGACY_IMPLEMENTATION.md` for the full account. In summary:
`opencv_openlensio_forward_point_corrected` (`Pipeline/ForwardConjugacy.lean`) now proves
the two-dimensional composed-function conjugacy this candidate called for, derived from —
not assumed as — the existing x/y pixel-level theorems (a new y-component theorem,
`opencv_openlensio_full_pipeline_pixel_corrected_y`, was required and proved first); the
abstract conjugacy-of-inverses identity (`conjugate_invOn`, `InverseConjugacy.lean`) and
its specialization (`opencv_openlensio_inverse_conjugate`,
`Pipeline/InverseConjugacyApplication.lean`) are also complete and kernel-checked. The
specialization's `D_CV⁻¹`-existence hypothesis is taken exactly as this section anticipated
— as an explicit, undischarged `Set.InvOn` hypothesis, not derived, since no injectivity
theorem for `distortPointCV` exists in this repository. This closes the specific gap this
candidate identified; it does **not** resolve SQ-CV-07, establish anything about
OpenLensIO's native `U`, or construct any finite inverse-coefficient set — see the
implementation document's explicit non-claims list. The analysis below is preserved as
originally written (it remains an accurate account of why this candidate was chosen).

**Original statement**: given forward maps related by coordinate conjugation,
`D_OTI = S_F ∘ D_CV ∘ S_F⁻¹` (which is, in substance, what
`opencv_openlensio_full_pipeline_pixel_corrected` already establishes, modulo it never
being packaged as a composed-function equality — §4), and given that `D_CV⁻¹` exists on
some domain (by hypothesis — not newly proved here, taken from whatever injectivity/
existence result applies), conclude `D_OTI⁻¹ = S_F ∘ D_CV⁻¹ ∘ S_F⁻¹` on the
correspondingly-scaled domain.

- **Existing declarations to reuse**: none directly — as noted in §4, no named `def`
  exists for the OTI-side forward map at all; this candidate's first prerequisite is
  introducing one (e.g. `distortPointOTI (l q : ...) (F : ℝ) : SensorPoint → SensorPoint`),
  then restating `opencv_openlensio_full_pipeline_pixel_corrected` as a composed-function
  equality `distortPointOTI l q F = (S_F) ∘ (distortPointCV k p) ∘ (S_F⁻¹)` rather than a
  fully-inlined real-number identity.
- **Necessary hypotheses**: `F≠0` (so `S_F` is invertible — trivial, already assumed
  everywhere); existence of `D_CV⁻¹` on the relevant domain (an additional hypothesis,
  not proved by anything in this repository for the actual rational model — see Test C's
  table).
- **Mathematical strength**: **a genuinely general, model-independent fact** — conjugation
  of inverses under an invertible coordinate change is a standard, easy-to-prove identity
  (`(S_F∘f∘S_F⁻¹)⁻¹ = S_F∘f⁻¹∘S_F⁻¹`, essentially immediate from `(g∘h)⁻¹=h⁻¹∘g⁻¹` applied
  twice, given each piece is invertible) — but **stating it correctly, with the right
  hypotheses, for *this* repository's actual objects would be new**, because no named
  function or composed-equality form of the forward map currently exists to state it about
  (§4).
- **Interoperability relevance**: this is the theorem that **correctly connects**
  proposition A to a statement *about* `D_CV⁻¹`/`D_OTI⁻¹` for the first time — without yet
  discharging anything about whether `D_OTI⁻¹`, once this conjugacy is stated, coincides
  with OpenLensIO's *native* `U`. **It would not resolve SQ-CV-07** — `D_CV⁻¹`/`D_OTI⁻¹`
  (the exact inverse of the OpenCV-shaped forward map) is still a different object from
  OpenLensIO's native `U` (an independently-parameterized approximation to that inverse,
  per the base spec's own framing, §3) unless a *separate* argument shows they coincide,
  which this candidate does not attempt.
- **Main Lean implementation obstacles**: (a) introducing the missing named OTI forward-map
  `def` (§4); (b) stating "`D_CV⁻¹` exists on this domain" in a way that doesn't silently
  assume more than is proved — the honest hypothesis is `Set.InjOn` on a specified domain
  plus a `Set.SurjOn`/range statement, neither of which is currently proved for the actual
  rational, two-dimensional, non-zero-tangential case (Test C's table — only partial,
  conditional injectivity exists; no existence/surjectivity at all for the rational model).
- **Genuinely new or repackaging?** **Genuinely new as a *statement*** (nothing like it
  exists in the repository today, and it would be the first theorem to mention an inverse
  of anything in `opencv_opentrackio_proofs/` or relate that inverse to
  `openlensio_semantics/`'s native `U`), but its **proof**, once correctly set up, is
  standard function-composition algebra — the value is in the connection it draws and the
  precise hypotheses it would force the repository to state explicitly, not in proof
  difficulty.

### Candidate 3 — certified numerical inversion (full rational model)

**Statement**: extend `inverse_approximation/InverseApproximation.lean`'s Banach-fixed-point
machinery (currently proved only for the simplified 3-radial/2-tangential **polynomial**
model, no denominator) to the actual 6-coefficient **rational** Brown-Conrady model used
by `openlensio_semantics/`, establishing existence/uniqueness and/or an approximation-error
bound for the *real* model's inverse.

**Precise additional mathematical work required** (none of which currently exists,
confirmed by inspection of `InverseApproximation.lean` and `InjectivityModel.lean`):

- **Rational denominator bounds**: a lower bound `|1+k2r²+k4r⁴+k6r⁶| ≥ δ > 0` on the
  working domain — strictly harder than the polynomial model's boundedness, since it
  requires controlling the denominator from *below*, not just the numerator from above.
- **Derivative/Lipschitz bounds for a quotient**: `Lrad`/`Mrad`-style bounds
  (`InverseApproximation.lean:88-92`) would need a quotient-rule derivation (as already
  done, for a different purpose, in `radialScale_mul_derivPos`,
  `InjectivityModel.lean:332-387` — reusable groundwork, not a full solution).
- **Domain invariance**: showing the fixed-point iteration stays not just inside a disk
  (as `inverse_step_maps_disk` does for the polynomial model) but inside a region where
  the denominator bound above continues to hold — a materially harder invariant-set
  argument than the polynomial case.
- **Existence and uniqueness**: a `D_exists_unique_preimage`-style theorem for the
  rational model, built on the above.
- **Approximation error**: an `inverse_approx_error`-style bound, re-derived with the
  rational model's Lipschitz constant.
- **Coordinate transformation of the certified bound**: folding the `F`/mm/pixel
  conversion machinery back in — explicitly flagged as **"Layer 5," out of scope**, by
  `inverse_approximation/README.md:61-62`, not yet attempted for even the polynomial model.

**Should this be recommended?** **Not as the next step.** This is a substantial,
multi-month-scale formalization effort (by the evident difficulty gap between the
polynomial and rational cases, and by this repository's own `docs/laps/` velocity on the
polynomial model alone — four separate slice directories,
`bounded-inverse-approximation`/`inverse-injectivity`/`inverse-existence`/`inverse-approx-error`).
Its necessity has **not** been established by this investigation: per §5.3, the schema
already offers a zero-inversion path to proposition C (dual-direction storage), and per
§6, whether any real consumer even needs numerical inversion at all (as opposed to
receiving a separately-fitted native set) is unverified. Recommending this expensive
formalization without first checking the much cheaper operational question (do producers
supply native D→U sets directly?) would not be justified by the evidence gathered here.

### Candidate 4 — a parser-to-semantics theorem

**Statement**: formally link the parser's decoded `Distortion.model : String` to "the
mathematical function a compliant consumer is supposed to evaluate" — e.g. a Lean function
`modelOf : Distortion → (SensorPoint → SensorPoint)` (or a sum-type `DistortionDirection`)
that dispatches to `undistortPoint` for `"Brown-Conrady D-U"` and to (a newly-introduced)
`distortPointOTI` for `"Brown-Conrady U-D"`, together with a theorem that this dispatch is
total and matches the schema's documented default.

- **Distinguishing interpretation from compliance**: this candidate would prove *this
  repository's own interpretation* of what each string means is internally consistent and
  total (every `Distortion` value maps to *some* well-defined function) — it would **not**
  prove that any real implementation honors this interpretation (that is §6's open
  question, and no Lean theorem can close it).
- **Existing declarations to reuse**: `Distortion`/`decodeDistortion` (parser),
  `undistortPoint` (native direction). The U→D direction again needs the missing named
  `def` from §4/Candidate 2.
- **Necessary hypotheses**: essentially none beyond totality of the string match (would
  need a default/`else` case for unrecognized `model` strings, since the schema permits
  arbitrary text beyond the two documented values — an honest totality obligation this
  candidate would surface that does not currently exist anywhere in the parser).
- **Mathematical strength**: low (a dispatch-function well-definedness fact) but genuinely
  **new** — it would be the first point anywhere in this repository where the parser's
  output is connected to the mathematical semantics at all. Currently, per §4, that
  connection is exactly zero.
- **Interoperability relevance**: makes proposition B's assumption (1) (§5.2) a checked
  Lean definition rather than an unexamined prose assertion, and gives Candidate 1 a
  non-trivial type to be phrased in terms of; does not touch proposition C or §7's
  negative result at all.
- **Main Lean implementation obstacles**: deciding what the dispatch function should
  return for the (schema-permitted) case of an unrecognized `model` string — a genuine,
  currently-unaddressed modeling decision, not just plumbing.

### Recommendation

**Primary next theorem: Candidate 2 (inverse conjugacy), scoped exactly as stated —
proving the composed-function conjugacy identity, with its existence/injectivity
hypotheses left as explicit, named hypotheses rather than discharged.**

Justification: Candidate 1 and Candidate 4 are valuable but low-content plumbing that
would not advance the mathematical state of SQ-CV-07 at all (they formalize an
interpretation, not a fact about interoperability). Candidate 3 is high-value but its
necessity is unestablished and its cost is large; pursuing it before the operational
question in §6/§9 is answered risks formalizing the wrong thing (e.g. if real producers
already supply native D→U sets directly, Candidate 3's entire numerical-inversion
machinery is unnecessary for the actual interoperability question). Candidate 2 is the
cheapest result that is **honestly new** (nothing today states anything about an inverse
of the OpenCV-conjugate forward map, or relates it to OpenLensIO's native `U`), that
**correctly exposes, rather than hides, the remaining gap** (its hypotheses, once written
down precisely, would make visible exactly which injectivity/existence facts are missing
for the rational model — turning Test C's table into an explicit Lean proof obligation
instead of a prose observation), and that **does not require deciding Candidate 3's
expensive scope question first**.

---

## 9. Phase 6 — Novelty and value assessment

| Category | Applies to which finding |
|---|---|
| **1. Novel mathematical result** | The rational-function non-existence result for the multi-coefficient radial map ("Test A, extended," §7) — a genuinely new, rigorous negative result not previously stated in this repository's artifacts, built from the classical degree-multiplicativity of rational-map composition (standard, not newly discovered as a technique) applied correctly to this specific family. (A withdrawn earlier claim invoking Abel–Ruffini for a stronger, radicals-level impossibility was not rigorously established — see the Test D correction — and is not counted here.) |
| **2. Useful new formal verification result** | Candidate 2, if implemented: the first Lean statement connecting a forward-conjugacy fact to an inverse-direction claim in this codebase. |
| **3. Genuine standards-interpretation finding** | The schema's array-of-`Distortion`-objects structure as a zero-inversion resolution path (§3, §5.3) — a normative-reading finding about the standard itself, independent of any Lean proof. |
| **4. Practical interoperability guarantee** | **None of the findings in this document establish one.** Proposition C remains unestablished; Candidate 3 (the only candidate that could approach a practical guarantee for the actual rational model) is explicitly not recommended as the next step. |
| **5. Restatement of established algebra** | Candidate 1 and Candidate 4 are substantially this — valuable as documentation-as-code, not as new mathematics. |

**Strongest defensible research claim following from the recommended theorem (Candidate 2,
if proved)**: "The same-direction coordinate-conjugacy already established between OpenCV
and OpenTrackIO's forward distortion models extends, under an explicit injectivity/
existence hypothesis on OpenCV's own forward map, to a conjugacy between their respective
inverses — making precise, for the first time in this repository, exactly what would need
to be proved about either side's invertibility for that conjugacy to say anything about
OpenLensIO's *native* undistortion function specifically."

**What that theorem would still fail to establish**, stated explicitly per the task's
instruction: it would **not** show that `D_CV⁻¹` (OpenCV's forward map, inverted) coincides
with OpenLensIO's native `U` — those remain two independently-defined objects (§3; one
derived algebraically from a conjugacy argument, the other an independently-calibrated
native model) unless a *further*, separate argument bridges them. It would **not**
establish proposition C. It would **not** resolve SQ-CV-07. It would **not** provide any
numerical procedure usable in practice (that is Candidate 3's job, not Candidate 2's).

**No claim of novelty is made for the underlying conjugacy identity itself**
(`(g∘h)⁻¹=h⁻¹∘g⁻¹`, applied to an invertible coordinate rescaling) — this is standard,
elementary function theory, and is presented as such. The novelty, such as it is, is in
correctly stating it for *this* repository's specific objects and hypotheses, not in the
abstract identity.

**If the most valuable result is a negative finding, say so**: it is. **The most valuable
finding in this entire investigation is the impossibility result of §7 ("Test A, extended"):
no exact, finite, Brown-Conrady-shaped *rational-function* conversion rule from forward
(U→D) coefficients to native (D→U) coefficients can exist, for any non-degenerate
distortion.** (Whether some *other*, non-rational closed form exists is left as genuinely
open — insufficient evidence, per the corrected Test D — not folded into this claim.) This
reframes SQ-CV-07 from "an open question awaiting either a formula or a maintainer
clarification" to "a question whose exact-rational-formula framing is provably
unanswerable, and whose real resolution lies in either numerical methods (already
prescribed by the spec) or a normative/operational decision about dual-direction data
transmission (a standards question, not a mathematics question)." This is arguably more
valuable than any single candidate theorem in §8, and is not contingent on proving any of
them, and — unlike the withdrawn Abel–Ruffini claim — carries no unverified genericity
assumption.

---

## 10. Remaining open questions

- Whether UE's `LiveLinkOpenTrackIO`/`CameraCalibrationCore` pipeline branches its
  distortion evaluation on the parsed `model` string, or ignores it — unresolved, closed-
  source, §6.
- Whether any real OpenTrackIO producer populates more than one `Distortion` array entry
  to supply both directions directly (§3, §5.3) — unresolved, no implementation evidence
  either way.
- Assumption (2) of §5.2 (whether `F,w,ws` are reconstructible by a consumer from the same
  sample a producer used) — not independently audited in this pass.
- Whether OpenLensIO's or OpenTrackIO's maintainers intend `"Brown-Conrady U-D"` to carry
  exactly the semantic reading assumed in §5.2's assumption (1) — still pending maintainer
  response (SQ-CV-06/07 outreach, 2026-08-15, unchanged by this investigation).
- Whether the existing partial injectivity results for the rational model
  (`InjectivityModel.lean`) can be extended to a genuine existence/uniqueness theorem
  without the full Candidate-3 machinery — not investigated here; a smaller-scoped
  question than Candidate 3 that might be worth a separate, cheaper investigation before
  committing to the full rational-model Banach argument.

---

## 11. Explicit statement on SQ-CV-07's status

**SQ-CV-07 is not resolved by this document**, consistent with the restriction governing
this investigation. Nothing here reinterprets "Brown-Conrady U-D" as "D-U" or vice versa;
nothing here claims the same-direction tangential algebra settled in the prior adversarial
pass needs to be reopened (it does not — this investigation did not find any evidence
contradicting it, and did not revisit it beyond the citations in §2-3); and nothing here
treats numerical agreement at the sampled points in §7's Test B as a proof of anything
beyond that specific example (it is offered as a counterexample to a specific claim,
exactly as requested, not as a general theorem). The P0/P1 audit, the LAPS report, and
`docs/specification-questions.md`'s recorded statuses are unchanged by this document, as
instructed.

---

## 12. Executive recommendation

**STATUS UPDATE: this recommendation has been implemented** — see
`audit/INVERSE_CONJUGACY_IMPLEMENTATION.md`. The text below is preserved as originally
written, as the rationale that was acted on, not as an outstanding to-do.

**The single most valuable next Lean theorem is the inverse-conjugacy statement of
Candidate 2** (§8): given the already-proved forward conjugacy
`D_OTI = S_F∘D_CV∘S_F⁻¹` and an explicit (not yet proved, honestly stated as a hypothesis)
injectivity/existence condition on `D_CV`, conclude the corresponding conjugacy for the
inverses. It is the cheapest theorem that is genuinely new, correctly exposes rather than
conceals the remaining gap to native D→U interoperability, and does not presuppose a
decision on the much larger Candidate 3 scope question.

**Evidence required before implementing it**: (a) a decision on whether to introduce the
missing named OTI-forward-map `def` (§4) as part of this work or as separate housekeeping;
(b) an explicit choice of which existing or new injectivity/existence hypothesis on
`D_CV` to assume (the rational model's existing partial results, Test C's table, are the
natural candidates, but none currently cover the general two-dimensional,
nonzero-tangential case unconditionally); and (c), before any larger follow-on investment
in Candidate 3, an attempt — outside Lean, via further implementation research or direct
inquiry to the OpenTrackIO maintainers alongside the pending SQ-CV-06 outreach — to
determine whether real producers already resolve proposition C by supplying a
separately-fitted native D→U `Distortion` entry, which would make Candidate 3's expensive
numerical-inversion formalization unnecessary for practical interoperability regardless of
its independent mathematical interest.

Sources consulted for the web-search-derived claims in §6 (Unreal Engine
`LiveLinkOpenTrackIO`/`CameraCalibrationCore`):
- [LiveLinkOpenTrackIO plugin API reference](https://dev.epicgames.com/documentation/unreal-engine/API/Plugins/LiveLinkOpenTrackIO?lang=en-US)
- [Break Live Link Open Track IOLens Distortion Coeff](https://dev.epicgames.com/documentation/unreal-engine/BlueprintAPI/Utilities/Struct/BreakLiveLinkOpenTrackIOLensDist-?lang=en-US)
- [Make Live Link Open Track IOLens](https://dev.epicgames.com/documentation/unreal-engine/BlueprintAPI/Utilities/Struct/MakeLiveLinkOpenTrackIOLens?lang=en-US)
- [FSphericalDistortionParameters API reference](https://dev.epicgames.com/documentation/unreal-engine/API/Plugins/CameraCalibrationCore/FSphericalDistortionParameters?lang=en-US)
- [Camera Lens Calibration Overview](https://dev.epicgames.com/documentation/en-us/unreal-engine/camera-lens-calibration-overview)
