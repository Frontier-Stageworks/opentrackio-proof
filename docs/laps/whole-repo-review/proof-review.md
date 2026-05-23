# Proof Review: opentrackio-proof — Whole-Repo Audit

## Verdict

**accepted with notes**

All proofs are accepted. No forbidden constructs. No vacuity detected. Notes flag
the junk-value semantics at F=0 in `angle_of_view_eq` (benign, documented), and
two honest limitation disclosures that are correctly placed as comments rather than
hidden.

---

## Scope

Three Lean modules, reviewed as a unit:

| Module | Files | Key theorems |
|---|---|---|
| `opentrackio_parser/` | 40+ Lean files | Encoder/decoder roundtrip, error correctness, normalization |
| `opencv_opentrackio_proofs/` | 10 Lean files | OpenCV→OpenTrackIO parameter conversion, pipeline iff |
| `openlensio_semantics/` | 10 Lean files | Semantic bridge, angle-of-view, FOV model |

---

## Forbidden Construct Check

- `sorry`: **absent** across all 60+ source files
- `admit`: **absent**
- `set_option warn.sorry false`: **absent**
- Unauthorized `axiom` or `constant`: **absent** (grep confirmed)
- `unsafe`: **absent**
- `partial`: **absent**

No sorry-warning suppression, no axiom/constant replacement of proof obligations.

---

## Theorem-by-Theorem Audit

### 1. `nat_repr_toNat?_some` — [NumericLiteralRoundtrip.lean](../../../opentrackio_parser/NumericLiteralRoundtrip.lean)

**Plain English:** For every natural number `n`, rendering it as its decimal string
and then parsing that string back as a natural number returns exactly `n`.

**Intended claim match:** yes — this is the foundational bridge theorem that all Nat
field roundtrip proofs depend on.

**Parameter audit:**

| Name | Role | Used? | Necessary? | Suspicious? | Notes |
|---|---|---|---|---|---|
| `n : Nat` | the number to round-trip | yes | yes | no | universally quantified |

**Conclusion audit:**
- Strong enough: yes — equality, not mere existence
- Not a proxy: yes — this is the direct claim
- Not test-shaped: yes — universal over all Nat

**Proof strategy:**
- First meaningful tactic: `simp only [Nat.repr, String.toNat?, ...]`
- Shape: unfold definitions, then delegate to helper chain H1–H8
- Strategy matches theorem shape: yes

**Hard step:** The hard step is `foldl_toDigits` (H6): proving that folding the
parser accumulator function over `Nat.toDigits 10 n` recovers `n`. This uses
strong induction (`Nat.strongRecOn`) and case-splits on whether `n / 10 = 0`.
The `toDigitsCore_eq` lemma (H3) is the load-bearing bridge between
`Nat.toDigitsCore` (the implementation fuel loop) and `Nat.toDigits` (the
inductive definition). The proof is sound.

**Automation review:**
- `interval_cases` used for `n < 10` base cases (0–9): appropriate, goal-shaped
- `omega` used for arithmetic bounds: appropriate
- `decide` for concrete character comparisons: appropriate
- Hard step (digit recovery) handled by structured induction, not blind automation

**Anti-pattern scan:**

| Anti-pattern | Found? | Evidence |
|---|---|---|
| Vacuity | no | |
| Weakened conclusion | no | full equality `= some n` |
| Tactic soup | no | layered H1–H8 helper structure is clean |
| Broad automation hiding hard step | no | automation is localized; induction exposed |
| Runtime failure replacing proof | no | |

**Verdict for this theorem:** accepted

---

### 2. `sampleNormalize_idempotent` — [NormalizationTheorems.lean](../../../opentrackio_parser/NormalizationTheorems.lean)

**Plain English:** Applying `sampleNormalize` twice produces the same result as
applying it once. The normalize function is idempotent.

**Intended claim match:** yes

**Proof strategy:**
- First meaningful tactic: `cases h : decodeSample j with`
- Shape: case split on decode success/failure
- Both branches: the ok branch rewrites using `encodeSample_roundtrip` (Slice 15.11
  engine); the error branch reduces to `sampleNormalize j = j`.
- Strategy matches theorem shape: yes

**Hard step:** `encodeSample_roundtrip` — the engine theorem that
`decodeSample (encodeSample s) = .ok s`. This is in `SampleEncoder` and is the
product of the entire Slice 15.x chain. The idempotency proof is a clean
two-line consumer of that engine.

**Anti-pattern scan:**

| Anti-pattern | Found? | Evidence |
|---|---|---|
| Vacuity | no | error branch requires `j` to have no valid decode |
| Weakened conclusion | no | equality, not mere existence |
| Statement laundering | no | canonical statement for the intended property |

**Verdict for this theorem:** accepted

---

### 3. Error correctness theorems — [ErrorCorrectness.lean](../../../opentrackio_parser/ErrorCorrectness.lean)

Five theorems covering `decodeProtocol`, `decodeTransform`, `decodePositiveRational`.

**Plain English pattern:** If a required field key is absent from a JSON object, the
decoder returns `.error (.missingField "fieldname")`.

**Intended claim match:** yes — these are the soundness-in-the-error-direction theorems.

**Proof strategy:** All five use `simp [decodeXxx, h]` where `h` is the
`lookup? "field" = none` hypothesis. `simp` reduces the decoder's pattern-match on
the absent key to the error branch directly.

**Automation review:**
- `simp` with explicit lemma name and single hypothesis: goal-shaped
- The decoder definitions are definitionally transparent to `simp`
- Hard step: none — these are shallow structural claims

**Anti-pattern scan:**

| Anti-pattern | Found? | Evidence |
|---|---|---|
| Test-shaped theorems | no | universally quantified over all `kvs : List (String × JsonValue)` |
| Unused hypotheses | `decodeTransform_missing_rotation` has `tj : JsonValue` | see note below |

**Note:** `decodeTransform_missing_rotation` takes `tj : JsonValue` with
`ht : lookup? "translation" = some tj`. The `tj` value itself is not used in the
proof — only `ht` is. However, `ht` is necessary to progress past the translation
decode step, and `tj` is necessary to state `ht`. The hypothesis is load-bearing,
not suspicious.

**Verdict for this group:** accepted

---

### 4. `principal_point_conversion_necessary` / `principal_point_conversion_iff` / `principal_point_conversion_2d_iff` — [PrincipalPointConversion.lean](../../../opencv_opentrackio_proofs/PrincipalPointConversion.lean)

**Plain English (2d_iff):** The OpenCV linear projection `fx·x + cx` equals the
OpenTrackIO screen projection `(ws/w)·(F·x + ΔPx) + ws/2` simultaneously in both
axes for all scene points if and only if F = (w/ws)·fx = (h/hs)·fy, ΔPx =
(w/ws)·(cx − ws/2), ΔPy = (h/hs)·(cy − hs/2).

**Intended claim match:** yes — this is the paper's principal-point conversion, stated
as a complete biconditional.

**Parameter audit (principal_point_conversion_2d_iff):**

| Name | Role | Used? | Necessary? | Suspicious? | Notes |
|---|---|---|---|---|---|
| `w, h` | image dimensions | yes | yes | no | |
| `w_shader, h_shader` | screen/shader dimensions | yes | yes | no | |
| `fx, fy` | OpenCV focal lengths | yes | yes | no | |
| `cx, cy` | OpenCV principal point | yes | yes | no | |
| `F` | OpenTrackIO focal length | yes | yes | no | |
| `ΔPx, ΔPy` | projection offsets | yes | yes | no | |
| `hw, hh, hw_s, hh_s` | nonzero guards | yes | yes | no | field_simp needs these |

**Hard step:** `principal_point_conversion_necessary` — the necessity direction.
Proved by specializing consistency at `x''=0` (gives the ΔPx equation) and `x''=1`
(adds F). After `field_simp [hw, hw_s]` clears denominators, `nlinarith` closes
the two resulting linear arithmetic goals. The witness strategy is minimal and correct.

**Special theorem — `buggy_principal_point_conversion_inconsistent`:**
This is a regression guard for a documented bug in an earlier version of the SMPTE
RIS paper. The old formula `ΔPx = (w/ws)·cx` (missing the centering term `−ws/2`)
produces a contradiction with the consistency condition under `w ≠ 0, ws ≠ 0`. The
proof correctly shows the two formulas force `ws = 0`, contradicting `hws`. This is
a strong, non-proxy theorem with clear intent.

**Anti-pattern scan:**

| Anti-pattern | Found? | Evidence |
|---|---|---|
| Weakened conclusion | no | full iff for 2d_iff |
| Over-strong hypotheses | no | all nonzero guards are necessary for field_simp |
| Statement laundering | no | the iff is the maximal claim |

**Verdict for this group:** accepted

---

### 5. `whole_radial_polynomial_iff` / `all_distortion_conversions_iff` — [DistortionConversion.lean](../../../opencv_opentrackio_proofs/DistortionConversion.lean)

**Plain English (whole_radial_polynomial_iff):** The OpenCV radial numerator
polynomial `k1·r² + k2·r⁴ + k3·r⁶` equals the OpenTrackIO polynomial
`l1·(F·r)² + l3·(F·r)⁴ + l5·(F·r)⁶` for all `r` if and only if
`l1 = k1/F², l3 = k2/F⁴, l5 = k3/F⁶`.

**Intended claim match:** yes

**Hard step (→ direction):** The proof specializes at r=1,2,3 to obtain three
equations in `l1·F², l3·F⁴, l5·F⁶`. The comment correctly identifies this as a
Vandermonde-like system (the 3×3 matrix has columns 1, 4, 9 from 1², 2², 3²).
`nlinarith` closes the system after `field_simp`. The coefficient uniqueness claim
is justified.

**`all_distortion_conversions_iff`:** Bundles all eight parameter conversions (six
radial + two tangential) into a single iff. Both the LHS (polynomial consistency)
and RHS (coefficient formulas) are fully general over all inputs. The proof reduces
to three sub-iffs plus a conjunction reorganization. This is the strongest possible
global distortion conversion theorem.

**Note on `radial_coefficients_imply_rational_factor_equality`:** This is correctly
identified as a one-way (→ only) theorem. The file comment explains why: the rational
factor equality is weaker than coefficient equality (different coefficients can yield
the same rational function). The one-way direction is not a proof weakness — it
reflects the correct mathematical relationship.

**Anti-pattern scan:**

| Anti-pattern | Found? | Evidence |
|---|---|---|
| Weakened conclusion | no | both iff theorems are maximal |
| Proxy property | no | the radial one-way theorem is correctly identified as weaker |
| Tactic soup | no | structured: field_simp + nlinarith |

**Verdict for this group:** accepted

---

### 6. `opencv_openlensio_full_pipeline_pixel_iff` — [Pipeline/PixelIff.lean](../../../opencv_opentrackio_proofs/Pipeline/PixelIff.lean)

**Plain English:** Given all eight parameter conversions hold (l_i = k_i/F^(2n),
q_i = p_i/F², F = (w/ws)·fx, ΔPx = (w/ws)·(cx − ws/2)), the full OpenCV pixel
x-output equals the full OpenLensIO pixel x-output for every normalized input point
*if and only if* ws/w = fx.

This is the paper's central claim: the coefficient conversions alone are necessary
but not sufficient for full pipeline agreement; the scale ratio ws/w = fx is the
exact additional condition required.

**Parameter audit (selected):**

| Name | Role | Used? | Necessary? | Suspicious? | Notes |
|---|---|---|---|---|---|
| `hp : p1 ≠ 0 ∨ p2 ≠ 0` | needed for → | yes | yes | no | without this, tangential term may be zero for all inputs, making ws/w = fx undetectable |
| `hden` | radial denominator nonzero | yes | yes | no | needed to divide |
| `hF_pos : 0 < F` | positivity of F | yes | yes | no | used by sufficiency direction |

**Conclusion audit:**
- The iff is the maximal claim: the scale condition is exact, not merely sufficient
- Not test-shaped: universally quantified over all (x', y') : ℝ
- Not a proxy: the pixel equality IS the intended property

**Proof strategy:**
- Constructor: split into → and ←
- → delegates to `pixel_eq_implies_tangential_gap` (isolates the gap term) then
  `tangential_gap_forces_scale` (closes to `ws/w = fx`)
- ← delegates to `opencv_openlensio_full_pipeline_pixel_sufficiency`

**Hard step (→):** `pixel_eq_implies_tangential_gap` uses `linear_combination`
with the radial ratio equality, tangential simplifications, and the principal offset
cancellation to extract `(fx − ws/w) · T(x', y') = 0` for all (x', y').
`tangential_gap_forces_scale` then specializes at (1,1) and (1,−1) for the p1≠0
case, and at (0,1) for the p2≠0 case. The case analysis is correct.

**Hard step (←):** `opencv_openlensio_full_pipeline_pixel_sufficiency` uses
`hscale : ws/w = fx` to derive `ws = w·fx`, then shows the radial numerator and
denominator agree at scaled radii, then closes by `field_simp + ring`. The
derivation of `hfx ≠ 0` from `hscale` is clean.

**Anti-pattern scan:**

| Anti-pattern | Found? | Evidence |
|---|---|---|
| Over-strong hypotheses | no | `hp` is load-bearing for uniqueness in → |
| Weakened conclusion | no | full iff |
| Broad automation hiding hard step | no | `linear_combination` exposes the algebraic structure |

**Verdict for this theorem:** accepted

---

### 7. Mutation tests — [MutationTests.lean](../../../opencv_opentrackio_proofs/MutationTests.lean)

24 theorems organized into groups A–I, each using a consistent
**Layer 1 (forces degeneracy) + Layer 2 (closes to False)** structure.

**Non-vacuity check:** Section I contains two existential sanity examples confirming
that the consistency hypotheses used in the mutation theorems are satisfiable. Example
I.1 gives a symbolic witness; example I.2 gives the numeric witness w=2, ws=1, fx=3,
cx=4 → F=6, ΔPx=7. Without these sanity checks, every mutation theorem would be
vacuously true.

**Verdict:** The mutation suite is well-designed and non-vacuous. accepted.

---

### 8. `angle_of_view_eq` — [AngleOfView.lean](../../../openlensio_semantics/AngleOfView.lean)

**Plain English:** The tangent of half the angle of view equals r_u / F.

**Theorem statement:**
```lean
theorem angle_of_view_eq (F r_u : ℝ) :
    Real.tan (angleOfView F r_u / 2) = r_u / F
```

**Proof:** `simp [angleOfView, Real.tan_arctan]` — unfolds `angleOfView` to
`2 · arctan(r_u/F)`, halves it to `arctan(r_u/F)`, and applies
`Real.tan_arctan : Real.tan (Real.arctan x) = x`.

**Junk-value note (flagged but benign):** The theorem is stated for all `F : ℝ`,
including F = 0. At F = 0: `r_u / 0 = 0` (Lean total division), `arctan(0) = 0`,
`tan(0) = 0`. Both sides equal 0, so the theorem holds with junk-value semantics.
The file explicitly documents this and states physical use requires F > 0, enforced
by `ValidLensSemantics`. This is the correct design choice: keeping the formal
theorem unconditioned while requiring callers to enforce F > 0.

**Anti-pattern scan:**

| Anti-pattern | Found? | Evidence |
|---|---|---|
| Vacuity | no | hypothesis space is all (F, r_u) : ℝ × ℝ, which is satisfiable |
| Over-strong hypotheses | no | no preconditions; clean universal statement |
| Junk-value at F=0 | noted | benign; documented; caller-enforced |

**Verdict for this theorem:** accepted with notes (junk-value semantics at F=0 is
benign but reviewers should be aware)

---

### 9. `semanticExtraction_sound` — [SemanticBridge.lean](../../../openlensio_semantics/SemanticBridge.lean)

**Plain English:** If `extractLensSemantics` returns `.ok s` for a set of parameter
values, then `s` satisfies `ValidLensSemantics` (i.e., its focal length is positive).

**Intended claim match:** yes

**Non-vacuity:** The error branch is reachable (focalLength ≤ 0 returns `.error`).
The theorem does not hold for all inputs — only successful ones. Correctly scoped.

**Proof strategy:**
- `unfold extractLensSemantics at h` + `split_ifs at h with hf`
- Positive branch: `simp only [Except.ok.injEq] at h` + `subst h` + `exact hf`
- Error branch: `h : Except.error _ = Except.ok s` — contradiction closed implicitly
  (the `split_ifs` error branch produces an unprovable goal that `simp` closes)

**Anti-pattern scan:**

| Anti-pattern | Found? | Evidence |
|---|---|---|
| Vacuity | no | error branch is reachable |
| Statement laundering | no | the theorem directly connects the guard to the semantic predicate |

**Verdict for this theorem:** accepted

---

## Module Topology Review

```
MODULE TOPOLOGY REVIEW:
- Does each touched Lean file have one clear semantic responsibility: yes
- Did the task create one file per slice: no (one file per semantic unit, not per slice)
- Did the task create a monolithic file: no
- Are helper lemmas located near their stable API use: yes
  (PixelIffHelpers.lean colocated with PixelIff.lean in Pipeline/)
- Are private/local lemmas kept private or in intentional helper modules: yes
  (H1–H8 in NumericLiteralRoundtrip.lean are all private)
- Are public compatibility imports preserved: yes
  (PipelineEquivalence.lean and PixelEquivalence.lean are clean re-export/alias files)
- Did import dependencies become broader than necessary: no
- Does the file layout make future proof repair easier: yes
```

No monolith risk. No oversplit risk. No file is named after a repair attempt, slice
number, or session. The `Pipeline/` subdirectory is a clean semantic decomposition
into: model definition, sufficiency, helper lemmas, and the final iff.

---

## Honest Limitation Disclosures (not defects)

Two explicit limitations are correctly placed in the code as comments, not hidden:

**1. Full end-to-end pipeline tangential composition:**
In [PixelEquivalence.lean](../../../opencv_opentrackio_proofs/PixelEquivalence.lean),
the file comment correctly notes that full end-to-end pipeline equivalence (composing
radial + tangential + linear projection) requires specifying how the tangential output
feeds into pixel coordinates in each model, and that the paper does not fully specify
this. The `opencv_openlensio_full_pipeline_pixel_iff` theorem in `Pipeline/PixelIff.lean`
addresses this — it is the paper's central claim proved — but the file-level note
refers to an earlier, pre-Pipeline/ formulation.

**2. `radial_coefficients_imply_rational_factor_equality` is one-way:**
The file comment correctly explains why this is not an iff: equal rational functions
do not force equal coefficients. The stronger coefficient-level theorems
(`whole_radial_polynomial_iff`) are the ones used downstream.

---

## Anti-Pattern Scan (Repository-Level)

| Anti-pattern | Found? | Evidence | Severity |
|---|---|---|---|
| Statement laundering | no | | |
| Vacuity | no | mutation sanity examples I.1/I.2 confirm satisfiability | |
| Weakened conclusion | no | | |
| Over-strong hypotheses | no | all nonzero guards are used by field_simp or division | |
| Unused hypotheses | minor | `tj` in `decodeTransform_missing_rotation` — structurally necessary | low |
| Unreadable specification | no | | |
| Test-shaped theorems | no | all key theorems are universally quantified | |
| Tactic soup | no | | |
| Broad automation hiding hard step | no | induction and linear_combination expose structure | |
| Algebra rewrite ping-pong | no | | |
| Misused `<;>` | no | not used | |
| Runtime failure replacing proof obligations | no | | |
| Verifier confusion | no | | |
| Fuel weakening total correctness | no | | |
| Junk-value semantics | noted | `angle_of_view_eq` at F=0 | low (documented) |

---

## Required Action

none — the proofs are accepted. The junk-value note on `angle_of_view_eq` is
informational. The honest limitation disclosures are correct and appropriately placed.

No repair, theorem strengthening, hypothesis cleanup, helper lemma extraction, or
annotation removal is needed.
