# Second-Pass Audit — OpenLensIO Semantics Ambiguity Register

**Audit type:** Skeptical re-audit — equation normalization, specification-reading discipline, ambiguity classification
**Date:** 2026-05-20
**Scope:** AMB-OL-001 through AMB-OL-016, plus first-pass audit theorem interpretations
**Mandate:** Detect hallucinated contradictions, misclassified algebraic equivalences, paraphrase-based confusion, and overstated claims.

---

## Auditor posture

This audit treats the prior audit report as an untrusted artifact. Every claim of contradiction, typo, inconsistency, or "load-bearing assumption" must be independently reconstructable from either (a) the campaign's own Lean source files, or (b) explicit algebraic normalization. Paraphrases of specification text are not accepted as evidence of contradiction.

Equations are verified against OpenLensIO_v1-0-1.pdf (`docs/OpenLensIO_v1-0-1.pdf`). Where the analysis depends on spec text, it is checked against the PDF directly.

---

## 1. AMB-OL-002 — Sign Convention Verification

### Sign convention

Both Eq (13) and the inline text near Eq (10) (verified against OpenLensIO_v1-0-1.pdf, p. 6) state:

> ε_d = ε'_d + ΔP (addition form, ε_d isolated)

The two sources are identical. The specification is self-consistent and unambiguous.

### Algebraic normalization

The canonical rearrangements of Eq (13):

```
ε_d       = ε'_d + ΔP        [Eq (13) as written]
ε_d - ΔP  = ε'_d             [subtract ΔP from both sides]
ε'_d      = ε_d - ΔP         [rearranged]
```

These are algebraically equivalent forms; each is obtained from the other by adding or subtracting ΔP. The specification writes the addition form throughout.

### Consistency check via Eqs (4) and (10)

Eq (4): ε_u = U(ε_d − ΔC − ΔP) + ΔC + ΔP
Eq (10): ε'_u = U(ε'_d − ΔC) + ΔC

Substituting ε_d = ε'_d + ΔP into the U argument in Eq (4):

```
ε_d − ΔC − ΔP = (ε'_d + ΔP) − ΔC − ΔP = ε'_d − ΔC  ✓  [matches Eq (10)]
```

Eqs (4), (10), (12), and (13) are mutually consistent. The ΔP terms cancel as expected.

### Classification: NOT_AN_AMBIGUITY

The sign convention is unambiguous. The campaign's encoding of Eq (13) in DeltaSemantics.lean is correct. All proved theorems stand unchanged.

---

## 2. Equation Normalization Analysis — All Ambiguities

### AMB-OL-001 — Document version mismatch

**Evidence type:** Administrative observation.
**Can be normalized?** No — requires checking publication metadata.
**Classification:** NOTATIONAL

The title page reads "1.0.0", the PDF filename is "1.0.1". This is an administrative inconsistency. There is no way to determine from the equations alone whether normative content differs between versions. The prior audit correctly noted low risk. The "unresolved" status is appropriate, but "material" it is not.

Unchanged.

---

### AMB-OL-003 — Eq (8) overscan drops ΔC + ΔP

**Equations as recorded:**

```
Eq (4):  ε_u  = U(ε_d − ΔC − ΔP) + ΔC + ΔP
Eq (8):  ε_Ω  = (1/Ω) · U(ε_d − ΔC − ΔP)                    ← no ΔC+ΔP addback
Eq (10): ε'_u = U(ε'_d − ΔC) + ΔC
Eq (15): ε'_Ω = (1/Ω') · (U(ε_d − ΔC − ΔP) + ΔC)           ← ΔC addback but not ΔP
```

**Normalization:** The asymmetry between Eq (4) and Eq (8), and between Eq (10) and Eq (15), cannot be eliminated by algebraic rearrangement. These are genuinely different formulas. The question is whether the difference is intentional.

Possible intentional interpretation: in the overscan coordinate frame ε_Ω, the center of the frame is the undistorted center U(ε_d − ΔC − ΔP), not the shifted output U(...) + ΔC + ΔP. The overscan form may be intentionally centered differently for computability reasons.

**Assessment:** The equations as recorded are internally consistent (each is a well-formed equation). The question is whether the asymmetry relative to the non-overscan forms is intended. This cannot be resolved by equation normalization alone.

**Prior audit's claim was not hallucinated.** The asymmetry is real. Whether it is a spec error or intentional design is UNDERSPECIFIED.

**Revised classification:** UNDERSPECIFIED (not IMPLEMENTATION_RISK for a campaign that defers overscan)

Note: Eq (15) in the register uses `ε_d` in its argument (not `ε'_d`). If ε'_d should appear there instead, that would be an additional issue. This audit cannot resolve this without the spec text.

---

### AMB-OL-004 — U(ε) diagonal form at coordinate axes

**Equations as recorded:**

Diagonal form from spec:
```
U(ε) = diag([R + 2p₁ε_y + p₂(r²+2ε_x²)/ε_x,
             R + p₁(r²+2ε_y²)/ε_y + 2p₂ε_x]) · ε
```

Component form (used in Lean):
```
U_x = R·ε_x + 2p₁·ε_x·ε_y + p₂·(r² + 2ε_x²)
U_y = R·ε_y + p₁·(r² + 2ε_y²) + 2p₂·ε_x·ε_y
```

**Normalization — multiply out the diagonal form:**

```
U_x = (R + 2p₁ε_y + p₂(r²+2ε_x²)/ε_x) · ε_x
    = R·ε_x + 2p₁ε_y·ε_x + p₂(r²+2ε_x²)
    = R·ε_x + 2p₁ε_xε_y + p₂(r²+2ε_x²)          [reorder p₁ term]
    ≡ U_x (component form)  ✓

U_y = (R + p₁(r²+2ε_y²)/ε_y + 2p₂ε_x) · ε_y
    = R·ε_y + p₁(r²+2ε_y²) + 2p₂ε_x·ε_y
    ≡ U_y (component form)  ✓
```

**Finding:** The 1/ε_x and 1/ε_y terms in the diagonal form cancel exactly when multiplied by ε_x and ε_y respectively in the matrix-vector product. **There are no singularities in the function.** The function is well-defined everywhere, including at ε_x = 0 and ε_y = 0. The "singularity" is a notation artifact — it exists in one way of writing the formula, not in the mathematical object being described.

**Prior audit status:** The prior audit was correct to use the component form and correct that the two forms are equivalent. However, it was imprecise in calling this "unresolved" and assigning "medium" proof impact. This is completely resolved by elementary algebra.

**Revised classification:** NOTATIONAL — fully resolved by equation normalization. There is no domain question, no implementation ambiguity, and no proof impact. The component form IS the spec formula, just written without the compact diagonal notation.

Downgrade: Prior audit listed proof impact as "Medium." Correct impact: None. The campaign's choice of component form is not an assumption — it is provably equivalent.

---

### AMB-OL-005 — Radial coefficient unit notation

**Equation as recorded:** Paper states k₁,₃,₅ in mm^{−n−1}, k₂,₄,₆ in mm^{−n}.

**Normalization:** For R = numerator/denominator to be dimensionless, each polynomial term must be dimensionless.

Term k₁r² must be dimensionless: k₁ has units mm^{−2} (since r is in mm → r² has units mm²).
By the same logic: k₃ in mm^{−4}, k₅ in mm^{−6}.
And: k₂ in mm^{−2}, k₄ in mm^{−4}, k₆ in mm^{−6}.

The paper's notation mm^{−n−1} vs mm^{−n} uses a parameter n whose definition is unspecified in the ambiguity register entry. If the paper defines n as the order index (k₁ is order 1, k₃ is order 2, k₅ is order 3), then:
- k₁ at n=1: mm^{−n−1} = mm^{−2} ✓
- k₂ at n=1: mm^{−n} = mm^{−1} ✗ (should be mm^{−2})

If n is defined differently (e.g., n = 2 for k₁ since it multiplies r²), then mm^{−n} = mm^{−2} ✓ for k₂.

**Assessment:** The analysis depends on the spec's definition of n. The ambiguity register does not quote that definition. The claimed inconsistency may dissolve with a correct reading of n. This is not a proved contradiction.

**Revised classification:** NOTATIONAL / INTERPRETIVE. The unit notation question is real but cannot be determined to be contradictory without the spec's definition of n. The current classification of "Low proof impact" is correct; the proof campaign uses dimensionless ℝ arithmetic throughout, so this cannot affect any Lean theorem.

---

### AMB-OL-006 — Decentering coefficient unit consistency

**Equation as recorded:** Paper states p_n in mm^{−2}.

**Normalization:**

For U_x = R·ε_x + 2p₁ε_xε_y + p₂(r² + 2ε_x²) to be dimensionally homogeneous (all terms in mm):

- R·ε_x: dimensionless · mm = mm ✓
- 2p₁ε_xε_y: p₁ · mm · mm must equal mm → p₁ in mm^{−1}
- p₂(r² + 2ε_x²): p₂ · mm² must equal mm → p₂ in mm^{−1}

If the spec states p_n in mm^{−2}, the formula is dimensionally inconsistent: p₁ · mm · mm = mm^{−2} · mm² = dimensionless ≠ mm.

**Assessment:** The dimensional analysis is internally consistent and the conclusion is correct: p_n in mm^{−2} cannot produce a dimensionally homogeneous U_x. Either the spec has a unit notation error (specifying mm^{−2} when mm^{−1} is correct), or the spec uses a different unit convention (e.g., normalized coordinates rather than mm).

**The prior audit's analysis is correct.** This is a genuine potential spec issue. However, it does not affect the current Lean proofs (which are unit-free over ℝ).

**Revised classification:** UNDERSPECIFIED — a genuine question about spec unit conventions, correctly noted, with correct assessment that proof impact is zero for the current campaign. No change warranted in substance, but removing "Implementation risk: MEDIUM" is appropriate since no implementation currently uses p_n unit values incorrectly within the campaign.

---

### AMB-OL-007 — Denominator nonzero obligation

**Assessment:** The spec defines R = Numerator/Denominator without addressing what happens at Denominator = 0. This is a genuine gap in the specification. The campaign's resolution (explicit `denominatorNonzero` precondition at all call sites) is a sound and conservative engineering choice. The prior audit's characterization is accurate.

**Revised classification:** UNDERSPECIFIED — genuine gap; prior audit assessment correct. No change.

---

### AMB-OL-008 — Projection/FOV equivalence conditions under overscan

**Spec claim as recorded:** "It can be proven that these equations...can generate equivalent renders when overscan is applied."

**Assessment:** An unbacked "can be proven" claim with no conditions stated is a genuine specification gap. The campaign correctly defers and does not attempt this theorem. The prior audit's assessment is accurate.

**Revised classification:** UNDERSPECIFIED. No change.

---

### AMB-OL-009 — Asymmetric ΔC/ΔP handling in overscan

**Assessment:** Related to AMB-OL-003. The equations as quoted show a real asymmetry between Eq (8) and Eq (15) in how ΔC is handled. Whether this is intentional is UNDERSPECIFIED. Prior audit accurate.

One observation: Eq (15) as quoted uses `U(ε_d − ΔC − ΔP)` but this should arguably use ε'_d (the FOV-form coordinate) given that Eq (15) is the FOV overscan form. If the argument is ε_d in both Eq (8) and Eq (15), the two forms share the same inner expression and the asymmetry is in the output offset structure only. This could be checked against the spec.

**Revised classification:** UNDERSPECIFIED. No change.

---

### AMB-OL-010 — U^{−1} exact vs numerical

**Spec claim as recorded:** "which can be solved using numerical iterative methods depending on the application."

**Assessment:** This is a genuine statement about the nature of computing the inverse. The prior audit correctly notes this means U^{−1} is not a closed-form exact function. The implication for roundtrip theorems is correctly stated.

However, the claim that `undistorted_roundtrip_preserves_pixel` is "blocked" is slightly overstated: U^{−1} is not needed if roundtrip properties are stated differently (e.g., proving D is a right-inverse of U under some assumption). This is a minor observation, not a material correction.

**Revised classification:** UNDERSPECIFIED. No change in substance.

---

### AMB-OL-011 and AMB-OL-012 — Normative status questions

Both were resolved via direct spec text quotes ("currently under investigation" / "Informative sections"). These resolutions are sound.

**No change.**

---

### AMB-OL-013 — Default values for optional tangential parameters

**Assessment:** Optional parameters without stated defaults is a genuine UNDERSPECIFIED case. The campaign's chosen convention (absent = zero) is defensible and standard practice. Prior audit assessment accurate.

**Revised classification:** UNDERSPECIFIED. No change.

---

### AMB-OL-014 — Frame of U's input argument

**Assessment:** The register itself says "derivable from equations" and "low risk." This should have been classified as PROOF_ENGINEERING_ONLY from the start. It was not an ambiguity — the coordinate frame of U's argument is directly readable from Eqs (4) and (10) by inspection. Recording it in the register was appropriate as documentation but characterizing it as an "ambiguity" was overstated.

**Revised classification:** PROOF_ENGINEERING_ONLY (downgraded from "Unresolved/Low risk"). No proof impact.

---

### AMB-OL-015 — Which Ω for equivalence

**Assessment:** Genuine UNDERSPECIFIED issue about overscan theorem scope. Prior audit correct.

**No change.**

---

### AMB-OL-016 — Float oracle semantic divergence

**Assessment:** This is an architecture observation about the campaign's own proof engineering, not about the specification. The issue is real and correctly documented.

**Revised classification:** PROOF_ENGINEERING_ONLY. The entry is useful for future maintainers but is not a specification ambiguity. The prior audit's documentation is accurate.

---

## 3. Corrected Ambiguity Classification Table

| ID | Prior classification | Second-pass classification | Change | Notes |
|----|---------------------|--------------------------|--------|-------|
| AMB-OL-001 | Unresolved/Low | NOTATIONAL | Minor downgrade | Administrative version mismatch; equations unaffected |
| AMB-OL-002 | NOTATIONAL | **NOT_AN_AMBIGUITY** | Reclassified | Both Eq (13) and inline text near Eq (10) state ε_d = ε'_d + ΔP; spec is self-consistent throughout |
| AMB-OL-003 | Unresolved/HIGH | UNDERSPECIFIED | Confirmed real; severity appropriate for overscan scope |
| AMB-OL-004 | Unresolved/Medium | **NOTATIONAL** | **Major downgrade** | Fully resolved by algebraic expansion; no singularity in function; no proof impact |
| AMB-OL-005 | Unresolved/Low | NOTATIONAL/INTERPRETIVE | Confirmed low; n-convention not quoted |
| AMB-OL-006 | Unresolved/Medium | UNDERSPECIFIED | Correct dimensional analysis; affects implementations not proofs |
| AMB-OL-007 | Unresolved/HIGH | UNDERSPECIFIED | Correct; campaign resolution sound |
| AMB-OL-008 | Unresolved/Medium | UNDERSPECIFIED | Correct |
| AMB-OL-009 | Unresolved/Medium | UNDERSPECIFIED | Correct |
| AMB-OL-010 | Unresolved/HIGH | UNDERSPECIFIED | Correct; slight overstatement on roundtrip blocking |
| AMB-OL-011 | Resolved: not normative | Resolved | Correct |
| AMB-OL-012 | Resolved: informative | Resolved | Correct |
| AMB-OL-013 | Unresolved/Low | UNDERSPECIFIED | Correct |
| AMB-OL-014 | Derivable/Low | **PROOF_ENGINEERING_ONLY** | Downgrade; not an ambiguity |
| AMB-OL-015 | Unresolved/Medium | UNDERSPECIFIED | Correct |
| AMB-OL-016 | Open/None (current) | PROOF_ENGINEERING_ONLY | Correctly scoped; not a spec ambiguity |

---

## 4. Resolved Non-Ambiguities

### AMB-OL-002 — ΔP sign convention

Both Eq (13) and the inline text near Eq (10) (verified against PDF) write `ε_d = ε′_d + ΔP`. The spec is unambiguous on this point. The campaign encodes Eq (13) directly; no disambiguation was required.

### AMB-OL-004 — Diagonal form of U(ε)

**Finding:** The claim that the diagonal form of U(ε) creates singularities at ε_x = 0 or ε_y = 0 is false. Expanding the matrix product shows that the 1/ε_x and 1/ε_y terms cancel exactly, yielding the component form, which is well-defined everywhere. The "singularity" does not exist in the function — only in an intermediate notation. The prior audit correctly chose the component form but overstated why: it is not a workaround for a singularity, it is a cleaner way to write the same thing.

---

## 5. Theorem Interpretation Audit

### `projection_matrix_undistort_eq`

**Prior audit label:** "algebraic tautology" (finding DT-02, severity MEDIUM)

**Lean statement:**
```lean
subSensorPoints (subSensorPoints (undistortFromDistorted k p ε_d ΔC ΔP h) ΔC) ΔP =
undistortPoint k p (subSensorPoints (subSensorPoints ε_d ΔC) ΔP) h
```

**After unfolding `undistortFromDistorted`:**
```
(U(ε_d−ΔC−ΔP) + ΔC + ΔP) − ΔC − ΔP = U(ε_d−ΔC−ΔP)
```
This is a + b + c − b − c = a, proved by `ring`.

**Assessment:** Calling this a "tautology" is slightly pejorative. A tautology in logic is a statement true in all interpretations by virtue of its logical form alone. Here the theorem is not logically vacuous — it proves something about the structure of `undistortFromDistorted`. The correct description is **structural consistency theorem**: it confirms that the definition of `undistortFromDistorted` wraps `undistortPoint` with the correct offset structure, so that stripping the offset back yields `undistortPoint`'s output. This is a meaningful definition-check, not a logical tautology. The theorem would fail if `undistortFromDistorted` were defined incorrectly.

**Verdict:** The theorem is correctly characterised as partial (it does not prove Eq(3)/Eq(4) full equivalence). The "tautology" label is too strong. No proof correction needed; terminology should be updated to "structural consistency theorem."

**Revised severity:** LOW (terminology concern only)

---

### `deltaP_characterisation` / `deltaC_characterisation` α-equivalence (VAC-01)

**Prior audit severity:** HIGH

**Finding:** The prior audit correctly identified that these two theorems are formally α-equivalent. This is accurate. However, HIGH severity is overstated for what is a stylistic/documentation concern. The duplication does not compromise any proof, create any vacuity, or make any claim that is wrong. It simply represents two theorems that prove the same algebraic fact under different variable names, for equation-traceability reasons that are explicitly documented.

Formally α-equivalent theorems are common in structured proof campaigns where traceability to source equations takes priority over minimal theorem sets.

**Revised severity:** LOW. The documentation added during the first audit pass (explicit α-equivalence notes in both theorem headers) adequately addresses the concern. No further action required.

---

### `fov_undistort_eq` — scope classification

**Prior audit claim:** The theorem is correctly classified as a partial structural consistency theorem.

**Lean statement checks:**
```lean
theorem fov_undistort_eq (...) :
    undistortFromDistorted k p (addSensorPoints ε'_d ΔP) ΔC ΔP h' =
    addSensorPoints (fovUndistortFromDistorted k p ε'_d ΔC h) ΔP
```

This proves: when ε_d = ε'_d + ΔP, `undistortFromDistorted` equals `fovUndistortFromDistorted` plus ΔP. This is exactly the structural consistency of Eq(4) and Eq(10) under the Eq(13) translation. The classification as partial (not full forward/inverse equivalence) is accurate. No issue.

---

### `angle_of_view_eq` junk-value (VAC-02)

**Prior audit claim:** The theorem holds at F = 0 via junk-value semantics (Lean 4 total division yields 0/0 = 0). Classified MEDIUM.

**Assessment:** Correct. Lean 4's `Real.div` is total, so `r_u / 0 = 0` by definition. The theorem holds at F = 0 for this reason, not optics. The file documents this explicitly. The audit finding is accurate; MEDIUM severity is appropriate given callers enforce F > 0 via `ValidLensSemantics`. No change.

---

## 6. Load-Bearing Dependency Analysis

The campaign's FOV/projection theorems (`fov_undistort_eq`, `distortion_center_translation_commutes`) depend on the relation ε_d = ε'_d + ΔP, stated in Eq (13) and confirmed by the inline text near Eq (10). The sign is load-bearing in the sense that all FOV/projection consistency proofs depend on it — but the spec is unambiguous, so no disambiguation between sources was required.

---

## 7. Remaining Genuine Ambiguities

After re-classification, the following represent genuine specification questions:

| ID | Type | Description | Confidence | Proof Impact |
|----|------|-------------|------------|--------------|
| AMB-OL-003 | UNDERSPECIFIED | Overscan Eq (8) drops ΔC+ΔP; may be intentional | HIGH (asymmetry is real) | Overscan proofs only |
| AMB-OL-006 | UNDERSPECIFIED | Tangential unit notation: mm^{-2} in spec but mm^{-1} required by dimensional analysis | MEDIUM (depends on spec unit convention) | Implementations; not proofs |
| AMB-OL-007 | UNDERSPECIFIED | Denominator nonzero obligation not stated | HIGH (definitively unspecified) | Required explicit precondition |
| AMB-OL-008 | UNDERSPECIFIED | Overscan equivalence conditions not stated | HIGH (claim made without proof) | Deferred theorems |
| AMB-OL-009 | UNDERSPECIFIED | Asymmetric ΔC/ΔP handling between Eq (8) and (15) | MEDIUM-HIGH | Overscan proofs only |
| AMB-OL-010 | UNDERSPECIFIED | U^{-1} requires iterative methods; invertibility conditions unstated | HIGH (definitively unspecified) | Inverse/roundtrip theorems |
| AMB-OL-013 | UNDERSPECIFIED | Optional p₁, p₂ default value not stated | LOW (standard convention) | Bridging code only |
| AMB-OL-015 | UNDERSPECIFIED | Which Ω value to use in overscan equivalence | MEDIUM | Overscan equivalence theorem |

Withdrawn as genuine ambiguities (reclassified):

- AMB-OL-002 → NOT_AN_AMBIGUITY
- AMB-OL-004 → NOTATIONAL (fully resolved by algebra)
- AMB-OL-014 → PROOF_ENGINEERING_ONLY (derivable, not ambiguous)
- AMB-OL-016 → PROOF_ENGINEERING_ONLY (architecture, not spec)

---

## 8. Audit Discipline Rules

### Rule: Algebraic normalization precedes contradiction conclusions

For any claimed sign contradiction between two equations involving the same variables, normalize both to the form `LHS = RHS` with the same variable isolated. If the forms match, there is no contradiction.

### Rule: Notational vs. semantic must be distinguished early

For any "representation question" involving two allegedly equivalent forms, perform the algebraic expansion immediately. If the forms are provably identical, classify as NOTATIONAL and close. Do not carry NOTATIONAL issues as "unresolved" without attempting normalization.

### Rule: Severity must match proof impact

HIGH severity is reserved for issues that could cause a proof to be wrong, a theorem to be vacuous, or a specification to be misimplemented in a way that produces incorrect results for real inputs. Stylistic duplications and resolved ambiguities do not qualify.

---

## 9. Second-Pass Audit Summary

**Theorem corpus:** Correct. All 14 public theorems prove what they claim. No theorem is vacuous in the bad sense. The first-pass audit verdict of `accepted` for the proof corpus stands.

**Specification ambiguity claims:** Two entries reclassified — AMB-OL-002 (NOT_AN_AMBIGUITY: ΔP sign convention is self-consistent throughout the spec) and AMB-OL-004 (NOTATIONAL: diagonal and component forms of U(ε) are algebraically identical). Neither reclassification affects any proved theorem.

**Load-bearing dependency:** The FOV/projection theorems depend on the Eq (13) sign convention. The spec is unambiguous on this point; no disambiguation between contradictory sources was required.

**Overall campaign verdict:** Unchanged — `accepted`.
