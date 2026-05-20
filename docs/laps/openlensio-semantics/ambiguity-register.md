---
name: openlensio-semantics-ambiguity-register
description: Ambiguity register for openlensio_semantics — tracks unresolved interpretation questions from OpenLensIO v1.0.1 paper
metadata:
  type: reference
---

# Ambiguity Register — `openlensio_semantics`

All ambiguities extracted directly from OpenLensIO v1.0.1 PDF
(file: `OpenLensIO_v1-0-1.pdf`, title page: "OpenLensIO Lens Model Version 1.0.0", dated 17 February 2025).

---

## AMB-OL-001 — Document version mismatch

**Status:** Unresolved  
**Paper location:** Title page / filename  
**What is unclear:** The document title page reads "OpenLensIO Lens Model Version 1.0.0" but the PDF filename used in this project is `OpenLensIO_v1-0-1.pdf`. It is unclear whether there are two distinct releases (1.0.0 and 1.0.1) with different normative content, or whether the filename was incremented without updating the title page.  
**Implementation risk:** Low — if equations changed between versions, all spec references may be off.  
**Proof impact:** Low if equations are identical; high if any normative equation differs between versions.  
**Can proofs proceed?** Yes, with a note that all references are to the document as read.  
**Proposed resolution:** Compare filename against any SMPTE or RIS publication index; check git history of the camdkit repo for the file to see when it appeared as 1.0.1.

---

## AMB-OL-002 — ϵ'_d sign inconsistency (MATERIAL)

**Status:** Unresolved — likely a typo in inline text  
**Paper location:** Section 3, inline text near Eq (10) vs Eq (13)  
**What is unclear:**
- Inline text near Eq (10) states: "where ϵ′_d = ϵ_d + ΔP"
- Eq (13) states: "ϵ_d = ϵ′_d + ΔP", which implies ϵ′_d = ϵ_d − ΔP (opposite sign)
- Only one can be correct.

**Mathematical analysis:** Eq (13)'s sign is consistent with the rest of the model:
- If ϵ′_d = ϵ_d − ΔP, then substituting into Eq (10): ϵ′_u = U(ϵ_d − ΔP − ΔC) + ΔC
- Adding ΔP: ϵ_u = ϵ′_u + ΔP = U(ϵ_d − ΔC − ΔP) + ΔC + ΔP ✓ (matches Eq 4)
- The inline text near Eq (10) is almost certainly a typo.

**Implementation risk:** HIGH — using the wrong sign inverts the ΔP offset direction for all FOV characterisation proofs.  
**Proof impact:** All theorems relating FOV and projection characterisations depend on this sign.  
**Can proofs proceed?** Yes, with the assumption that Eq (13) is authoritative over the inline text. This assumption must be stated explicitly in any theorem that uses ϵ′_d.  
**Proposed resolution:** Confirm with paper authors or check against reference implementation output for nonzero ΔP cases.

---

## AMB-OL-003 — Eq (8) overscan drops ΔC + ΔP (MATERIAL)

**Status:** Unresolved  
**Paper location:** Section 2.1, Eq (8) vs Eq (4)  
**What is unclear:**
- Eq (4) (undistortion, projection): `ϵ_u = U(ϵ_d − ΔC − ΔP) + ΔC + ΔP`
- Eq (8) (overscan, projection): `ϵ_Ω = (1/Ω) · U(ϵ_d − ΔC − ΔP)`
- Eq (8) does NOT add back `ΔC + ΔP` after the undistortion. This differs from the non-overscan form.
- Compare also Eq (15) (FOV + overscan): `ϵ′_Ω′ = (1/Ω′) · (U(ϵ_d − ΔC − ΔP) + ΔC)` which does include `+ ΔC` but not `+ ΔP`.

**Implementation risk:** HIGH — if this is an error in the paper, overscan proofs based on Eq (8) will prove a theorem about the wrong model.  
**Proof impact:** Any theorem about projection/FOV equivalence under overscan requires a consistent definition of both forms. If Eq (8) is truly different from the non-overscan form in its handling of offsets, the equivalence theorem requires careful preconditions.  
**Can proofs proceed?** Only for the definition as written. Mark all Eq (8)-dependent theorems as assumption-gated pending resolution.  
**Proposed resolution:** Check reference implementations (Mo-Sys C++, CamDKit) to see how they implement overscan. Confirm with paper authors whether the `+ ΔC + ΔP` drop is intentional.

---

## AMB-OL-004 — U(ϵ) singular diagonal form at coordinate axes

**Status:** Unresolved representation question  
**Paper location:** Section 4.1, Eq (16)  
**What is unclear:** Eq (16) writes U as a diagonal matrix times ϵ:

```
U(ϵ) = diag([R + 2p₁ϵ_y + p₂(r² + 2ϵ_x²)/ϵ_x,
              R + p₁(r² + 2ϵ_y²)/ϵ_y + 2p₂ϵ_x]) · ϵ
```

The diagonal entries contain `1/ϵ_x` and `1/ϵ_y`, which are undefined when ϵ_x = 0 or ϵ_y = 0 respectively. The non-singular component form:

```
U_x(ϵ) = R·ϵ_x + 2p₁ϵ_xϵ_y + p₂(r² + 2ϵ_x²)
U_y(ϵ) = R·ϵ_y + p₁(r² + 2ϵ_y²) + 2p₂ϵ_xϵ_y
```

is equivalent away from the axes and has no singularities.

**Implementation risk:** The diagonal form is a compact notation; the actual function is the component form. However, the paper uses the diagonal form without comment.  
**Proof impact:** Lean definitions must use the component (non-singular) form. Theorem statements about U should not depend on the diagonal form. Any domain-safety proof must note that the component form is the intended definition.  
**Can proofs proceed?** Yes — use component form. Document the choice in the proof capsule.  
**Proposed resolution:** Use component form as the Lean definition. State explicitly that the diagonal form in the paper is a notational convenience.

---

## AMB-OL-005 — Radial coefficient unit notation

**Status:** Unresolved  
**Paper location:** Section 4.1, paragraph after Eq (17)  
**What is unclear:** Paper states "k₁,₃,₅ in units of mm^{−n−1}, k₂,₄,₆ in units of mm^{−n}". For R to be dimensionless, both numerator polynomial `1 + k₁r² + k₃r⁴ + k₅r⁶` and denominator `1 + k₂r² + k₄r⁴ + k₆r⁶` must be dimensionless. This requires kᵢ paired with r^{2m} to have units mm^{−2m}, i.e.:
- k₁: mm^{−2}, k₃: mm^{−4}, k₅: mm^{−6}
- k₂: mm^{−2}, k₄: mm^{−4}, k₆: mm^{−6}

All six coefficients have units mm^{−2m} for their respective m. The "mm^{−n−1}" vs "mm^{−n}" distinction in the paper is inconsistent with dimensional analysis unless the paper uses a different convention for n.  
**Implementation risk:** LOW for the polynomial itself; potentially misleading for unit-aware implementations.  
**Proof impact:** Unit tracking in the formal model. If the Lean model carries units as phantom types, the unit class of each coefficient must be specified correctly.  
**Can proofs proceed?** Yes, using dimensionless-per-term analysis. State the unit assumption explicitly.  
**Proposed resolution:** Treat all six k coefficients as having units mm^{−2m} for the m-th power term; treat the paper's "mm^{−n}" notation as using n=2m.

---

## AMB-OL-006 — Decentering coefficient p_n unit consistency

**Status:** Unresolved  
**Paper location:** Section 4.1, paragraph after Eq (17)  
**What is unclear:** Paper states p_n "in units of mm^{−2}". Standard Brown-Conrady tangential formula adds:
- `2p₁ϵ_xϵ_y`: mm^{−2} · mm · mm = dimensionless
- `p₂(r² + 2ϵ_x²)`: mm^{−2} · mm² = dimensionless

But U_x must output mm, not dimensionless. If U_x = R·ϵ_x + (dimensionless tangential terms), only the R·ϵ_x term is in mm.

The full formula is `U_x = R·ϵ_x + 2p₁ϵ_xϵ_y + p₂(r²+2ϵ_x²)`. For this to be in mm with p_n in mm^{−2}: the tangential term `2p₁ϵ_xϵ_y` is dimensionless, which cannot be added to mm. This requires p_n to be in mm^{−1} for units to be consistent (`mm^{−1} · mm · mm = mm`).

**Implementation risk:** MEDIUM — incorrect unit assumption leads to a model where the distortion function is dimensionally inconsistent.  
**Proof impact:** Domain predicates for valid coefficient ranges may carry incorrect units.  
**Can proofs proceed?** Yes, but mark all tangential-coefficient-dependent theorems as carrying the assumption `p_n has units mm^{−1}` (not mm^{−2} as stated).  
**Proposed resolution:** Check against CamDKit or Mo-Sys reference implementation for the actual unit convention used.

---

## AMB-OL-007 — Denominator nonzero: producer vs consumer obligation

**Status:** Unresolved  
**Paper location:** Section 4.1, Eq (17)  
**What is unclear:** The radial term `R = Numerator / Denominator` where `Denominator = 1 + k₂r² + k₄r⁴ + k₆r⁶`. The paper does not state:
- Whether producers are responsible for ensuring the denominator is nonzero;
- Whether consumers must reject inputs with zero denominator;
- Whether the denominator can be zero for any valid input;
- What should happen if the denominator is zero.  
**Implementation risk:** HIGH — if a proof of domain safety omits the nonzero condition, the distortion function is partial and theorems about it may be vacuous or false.  
**Proof impact:** All theorems about R and U(ϵ) require the denominator nonzero as a hypothesis. The semantic validity predicate `ValidDistortionCoefficients` must include this condition.  
**Can proofs proceed?** Yes — state the denominator nonzero condition as an explicit precondition on all theorems that use R.  
**Proposed resolution:** Treat nonzero denominator as a semantic validity requirement on the coefficient tuple `(k₁, k₂, k₃, k₄, k₅, k₆)` for all r in the domain of use.

---

## AMB-OL-008 — Projection/FOV equivalence conditions under overscan

**Status:** Unresolved  
**Paper location:** Section 3.1, final paragraph  
**What is unclear:** Paper states: "It can be proven that these equations for the field of view and projection matrix characterisations can generate equivalent renders when overscan is applied, but overscan computed on one form is not guaranteed to fill the screen of the other form." The conditions under which the renders are equivalent are not stated. The "can be proven" claim has no proof, no reference, and no preconditions listed.  
**Implementation risk:** MEDIUM — attempting to prove equivalence without the correct preconditions will fail or require the wrong hypotheses.  
**Proof impact:** The `projection_fov_equiv` theorem is blocked until equivalence conditions are known.  
**Can proofs proceed?** Partially — the two models can be defined independently and shown to be related by translation (Eqs 12, 13) without needing full equivalence.  
**Proposed resolution:** Attempt to derive the equivalence conditions algebraically from Eqs (4), (8), (10), (15) and mark the theorem as assumption-gated on those conditions.

---

## AMB-OL-009 — Asymmetric ΔC/ΔP handling in overscan equations

**Status:** Unresolved  
**Paper location:** Section 2.1 Eq (8) vs Section 3.1 Eq (15)  
**What is unclear:**
- Eq (8): `ϵ_Ω = (1/Ω) · U(ϵ_d − ΔC − ΔP)` — neither ΔC nor ΔP added back
- Eq (15): `ϵ′_Ω′ = (1/Ω′) · (U(ϵ_d − ΔC − ΔP) + ΔC)` — ΔC added back but not ΔP
- Non-overscan projection Eq (4): adds back `+ ΔC + ΔP`
- Non-overscan FOV Eq (10): adds back `+ ΔC`

The asymmetry between the overscan forms and their non-overscan counterparts, and between the two overscan forms with each other, is not explained in the paper.  
**Implementation risk:** MEDIUM — overscan-dependent theorems will have inconsistent preconditions if the asymmetry is not resolved.  
**Proof impact:** Any overscan containment or equivalence theorem must explicitly model this asymmetry or be scoped to the specific equation used.  
**Can proofs proceed?** Only for definitions as written, without claiming cross-form equivalence.  
**Proposed resolution:** Derive the overscan equations from first principles (what does "overscan renders the same image" mean formally) and check against Eqs (8) and (15).

---

## AMB-OL-010 — U^{−1} as exact inverse vs numerical approximation

**Status:** Unresolved  
**Paper location:** Section 3, following Eq (11)  
**What is unclear:** The paper states for Eq (11): "which can be solved using numerical iterative methods depending on the application." This characterises `U^{−1}` as an approximation computed numerically, not an exact closed-form inverse. For formal proofs of roundtrip properties (`ϵ_u → ϵ_d → ϵ_u`), we need U to be injective. The paper does not state conditions under which U is globally invertible.  
**Implementation risk:** HIGH — any roundtrip theorem that uses `U^{−1}` as an exact function would be proving something stronger than the paper supports. A formal model of U^{−1} as a numerical approximation requires different machinery.  
**Proof impact:** `undistorted_roundtrip_preserves_pixel` and all inverse-dependent theorems are assumption-gated on an injectivity or local invertibility assumption.  
**Can proofs proceed?** Yes for forward direction only (U applied to specific inputs). Inverse direction requires explicit injectivity hypothesis.  
**Proposed resolution:** State injectivity of U as a project-level assumption, note it is not proved in the paper, and consider it an implementation-supported conjecture pending formal analysis.

---

## AMB-OL-011 — Aperture formula (Section 4.3) normative status

**Status:** Resolved — NOT normative  
**Paper location:** Section 4.3, preceding Eq (19)  
**What is clear:** Paper explicitly states: "The accuracy of the following accepted expression for circle of confusion is currently under investigation."  
**Decision:** Eq (19) is not normative. It must not appear in the first proof campaign. Defer entirely.

---

## AMB-OL-012 — Overscan appendix (Section A.1) normative status

**Status:** Resolved — informative only  
**Paper location:** Section A header: "Informative sections"  
**What is clear:** Section A is explicitly labelled "Informative sections." Eqs (21)–(24) describe how to compute ideal overscan but are advisory, not required.  
**Decision:** Eqs (21)–(24) may be modelled as a reference algorithm but must not be treated as normative proof targets. Any overscan containment theorem based on these equations must be clearly labelled as based on an informative (non-normative) section.

---

## AMB-OL-013 — Default values for optional tangential parameters p₁, p₂

**Status:** Unresolved  
**Paper location:** Section 1.3, parameter table  
**What is unclear:** p₁ and p₂ are listed as optional dynamic parameters. The paper does not explicitly state that they default to zero when absent. In the `opentrackio_parser`, `Distortion.tangential` is `Option (NonemptyArray String)`, so absent tangential means the array is `none`. The semantic layer must decide how to interpret absent p₁, p₂ in the distortion model.  
**Implementation risk:** LOW — if absent = zero, the simplification is clean.  
**Proof impact:** The `tangential_zero_coefficients_identity` theorem requires either explicit zero or explicit treatment of the optional case.  
**Can proofs proceed?** Yes, with the explicit assumption that absent p_n = 0.  
**Proposed resolution:** Treat absent p₁, p₂ as zero in the semantic model. State this as a semantic bridge convention.

---

## AMB-OL-014 — Frame of U's input argument (distortion-centered frame)

**Status:** Low risk — derivable from equations  
**Paper location:** Sections 2, 3, 4.1  
**What is unclear:** Eq (16) defines U(ϵ) where ϵ is a screen coordinate vector. In Eqs (4) and (10), U is always called with `ϵ_d − ΔC − ΔP` or `ϵ′_d − ΔC`. The paper does not explicitly state that U's argument is in the coordinate frame centered at the distortion center. This must be derived.  
**Proof impact:** The semantic model should represent U as a function of distortion-centered coordinates to make the domain specification clean.  
**Can proofs proceed?** Yes — derivable. State as a documentation note in the proof capsule.

---

## AMB-OL-015 — Overscan equivalence: which form's overscan factor to use

**Status:** Unresolved  
**Paper location:** Section 3.1, final sentence  
**What is unclear:** Paper states: "overscan computed on one form is not guaranteed to fill the screen of the other form." This means Ω (for projection characterisation) and Ω′ (for FOV characterisation) are different values even for the same lens. Any formal proof of equivalence must track which Ω is used with which form.  
**Proof impact:** Cannot prove a single `overscan_containment` theorem without specifying which form's Ω is used.  
**Can proofs proceed?** Yes — separately for each characterisation, with distinct Ω and Ω′.

---

## Summary Table

| ID | Title | Status | Proof Impact | Can Proceed? |
|----|-------|--------|--------------|--------------|
| AMB-OL-001 | Version mismatch | Unresolved | Low | Yes |
| AMB-OL-002 | ϵ′_d sign | Likely typo in inline text | HIGH | Yes, with Eq (13) as authority |
| AMB-OL-003 | Eq (8) drops ΔC + ΔP | Unresolved | HIGH | Assumption-gated |
| AMB-OL-004 | Diagonal U singularity | Representation choice | Medium | Yes, use component form |
| AMB-OL-005 | Radial coeff units | Unresolved | Low | Yes, with unit assumption |
| AMB-OL-006 | Decentering coeff units | Unresolved | Medium | Yes, with unit assumption |
| AMB-OL-007 | Denominator nonzero | Unresolved | HIGH | Yes, as explicit precondition |
| AMB-OL-008 | FOV/proj equivalence conditions | Unresolved | Medium | Partial |
| AMB-OL-009 | Asymmetric ΔC/ΔP in overscan | Unresolved | Medium | Scoped only |
| AMB-OL-010 | U^{−1} exact vs numerical | Unresolved | HIGH | Forward only |
| AMB-OL-011 | Aperture normative? | Resolved: NOT normative | — | Defer |
| AMB-OL-012 | Overscan appendix normative? | Resolved: informative | Low | Advisory only |
| AMB-OL-013 | Default p₁, p₂ = 0 | Unresolved | Low | Yes, with assumption |
| AMB-OL-014 | U argument frame | Derivable | Low | Yes |
| AMB-OL-015 | Which Ω for equivalence | Unresolved | Medium | Separately per form |
