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

## AMB-OL-002 — ϵ'_d sign relationship

**Status:** Resolved — NOT_AN_AMBIGUITY  
**Paper location:** Section 3, inline text near Eq (10) and Eq (13)

Both Eq (13) and the inline text near Eq (10) (verified against OpenLensIO_v1-0-1.pdf, p. 6) state:
- `ϵ_d = ϵ′_d + ΔP` (addition form, ϵ_d isolated)

The two sources are identical. The specification is self-consistent and unambiguous throughout.

**Mathematical check:** Substituting Eq (13) into Eq (4):
- U(ε_d − ΔC − ΔP) = U((ε'_d + ΔP) − ΔC − ΔP) = U(ε'_d − ΔC) ✓ (matches Eq 10)

**Proof impact:** None. The sign convention is encoded correctly in DeltaSemantics.lean; all theorems stand.  
**Implementation risk:** None — the specification is unambiguous.

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

## AMB-OL-004 — U(ϵ) diagonal form notation

**Status:** Resolved — NOTATIONAL (see `second-pass-audit.md`)  
**Paper location:** Section 4.1, Eq (16)

**Resolution (2026-05-20):** The apparent singularities at ϵ_x = 0 and ϵ_y = 0 in the diagonal form do not exist in the actual function. The 1/ϵ_x and 1/ϵ_y terms in the diagonal entries cancel exactly when multiplied by the corresponding components. Expanding:

```
diag-entry-x · ϵ_x = [R + 2p₁ϵ_y + p₂(r² + 2ϵ_x²)/ϵ_x] · ϵ_x
                    = R·ϵ_x + 2p₁ϵ_xϵ_y + p₂(r² + 2ϵ_x²)   ← no ϵ_x in denominator

diag-entry-y · ϵ_y = [R + p₁(r² + 2ϵ_y²)/ϵ_y + 2p₂ϵ_x] · ϵ_y
                    = R·ϵ_y + p₁(r² + 2ϵ_y²) + 2p₂ϵ_xϵ_y   ← no ϵ_y in denominator
```

These are exactly the component forms. The diagonal notation is a compact factoring of the component formula; the two representations are algebraically identical and the function is continuous everywhere. There is no singularity in the function — only in the intermediate notation.

**Implementation risk:** None — the component form is unambiguous and continuous.  
**Proof impact:** None — the Lean definitions use the component form, which is correct. No theorem depends on the diagonal representation.

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

**Status:** Partially resolved — framing corrected after re-reading spec (2026-05-24)  
**Paper location:** Section 3, Eqs (5) and (11)

**Framing correction:** The original framing said the paper "characterises U^{−1} as an approximation computed numerically." This is imprecise. Reading the spec directly:

- Eq (5): `ε_d = U⁻¹(ε_u − ΔC − ΔP) + ΔC + ΔP`
- Eq (11): `ε′_d = U⁻¹(ε′_u − ΔC) + ΔC`, "which can be solved using numerical iterative methods depending on the application."

The spec DOES define D = U⁻¹ as a mathematical object in both equations. It asserts D exists. The numerical iteration note is about *computing* D at a specific input — not about whether D is defined. The spec treats U as invertible without proving it.

**What is actually open:** The Lean formalization challenge is that there is no closed-form formula for D for the full Brown-Conrady model. In Lean, to use D you must either: (a) construct D nonconstructively via `Function.invFun` given injectivity — which is now proved in several regimes in `InjectivityModel.lean` (UI-00 through UI-03), yielding `D ∘ U = id` by injectivity alone; or (b) find a closed-form D for a restricted subclass and prove it (which UI-04 did for p=0 with `radialDescale`).

**Remaining open:** Proving U is surjective onto its intended range (needed for `U ∘ D = id` in the `Function.invFun` sense). Global injectivity without the caller-supplied `hScaleInj` hypothesis. These are the actual open gates, not D's definition.

**Implementation risk:** Medium — a nonconstructive `D ∘ U = id` theorem is reachable from existing injectivity results. The right-inverse direction requires surjectivity, which is not yet addressed.  
**Proof impact:** Revised. `undistortPoint_injective_pure_radial` and related results in `InjectivityModel.lean` provide the injectivity needed for a nonconstructive left-inverse theorem. The concrete conditional left inverse for p=0 is proved as `radialDescale_left_inverse_zero_tangential`.  
**Can proofs proceed?** Yes — left-inverse direction is substantially proved. Right-inverse requires surjectivity machinery not yet in scope.  
**Proposed resolution:** State the nonconstructive `D ∘ U = id` theorem via `Function.invFun` as the next reachable step. Surjectivity for the right-inverse direction is the remaining open gate.

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

**Status:** Resolved — PROOF_ENGINEERING_ONLY (see `second-pass-audit.md`)  
**Paper location:** Sections 2, 3, 4.1  
**What is unclear:** Eq (16) defines U(ϵ) where ϵ is a screen coordinate vector. In Eqs (4) and (10), U is always called with `ϵ_d − ΔC − ΔP` or `ϵ′_d − ΔC`. The paper does not explicitly state that U's argument is in the coordinate frame centered at the distortion center. This must be derived from the call sites.  
**Resolution:** The coordinate frame is fully derivable from the equations. The call sites in Eqs (4) and (10) are the authoritative specification; no ambiguity remains once these are read carefully. This is a proof-engineering note, not a genuine specification gap.  
**Proof impact:** The semantic model uses distortion-centered coordinates as U's argument — derivable, documented in the proof capsule. No theorem is weakened by this.  
**Can proofs proceed?** Yes — derivable and resolved.

---

## AMB-OL-015 — Overscan equivalence: which form's overscan factor to use

**Status:** Unresolved  
**Paper location:** Section 3.1, final sentence  
**What is unclear:** Paper states: "overscan computed on one form is not guaranteed to fill the screen of the other form." This means Ω (for projection characterisation) and Ω′ (for FOV characterisation) are different values even for the same lens. Any formal proof of equivalence must track which Ω is used with which form.  
**Proof impact:** Cannot prove a single `overscan_containment` theorem without specifying which form's Ω is used.  
**Can proofs proceed?** Yes — separately for each characterisation, with distinct Ω and Ω′.

---

## AMB-OL-016 — Float oracle semantic divergence from exact-real definitions (MATERIAL)

**Status:** Open — documented risk, no resolution planned for current campaign
**Source:** Vacuity audit finding EX-01 (2026-05-20)
**Relevant files:** `ExecutableSemanticOracle.lean` (SLICE-OL-14), `battery-tester/semantic_oracle/reference_oracle.py` (SLICE-OL-15)

**What is the divergence:**

1. **Domain-validity architecture mismatch.** The exact-real layer encodes domain validity as a Prop-level precondition (`h : denominatorNonzero k r`) embedded in function signatures. The Float oracle encodes it as an `Option` return: `radialTerm_float` returns `none` when the denominator is within absolute tolerance `1e-10` of zero. These are structurally incompatible — the Float oracle cannot directly call exact-real functions, and there is no Lean theorem connecting the two validity mechanisms.

2. **Tolerance-based vs. exact nonzero.** `denominatorNonzero` requires the denominator is exactly ≠ 0 over ℝ. `radialTerm_float` uses `denom.abs < 1e-10` as its rejection threshold. This creates two distinct failure modes:
   - A denominator with |d| < 1e-10 is rejected by the Float oracle but satisfies `denominatorNonzero` (if d ≠ 0 exactly).
   - A denominator with |d| >> 1e-10 but very close to zero in practice is accepted by the Float oracle but may produce large floating-point errors.
   Neither failure mode is captured by the current Lean semantics.

3. **Function signature divergence.** `undistortX_float` takes a pre-computed `R : Float` (the radial term, already unwrapped from `Option`). The exact `undistortX` takes `h : denominatorNonzero` and calls `radialTerm` internally. Any bridging theorem would need to relate a post-match `Float` value to an ℝ-level division by a nonzero denominator — this requires a Float-to-ℝ correctness claim not present in the campaign.

4. **No Float↔ℝ bridging theorem.** No Lean theorem in the campaign connects the Float oracle's output to the exact-real definitions. The `ExecutableSemanticOracle.lean` file carries a prominent warning: `⚠ FLOAT APPROXIMATION ONLY — NOT A PROVED THEOREM ⚠`.

**Role of the executable oracle:**
The Float oracle and Python reference oracle are **differential-testing infrastructure** — they provide executable computation against hand-computed expected values for confidence. They are NOT verified executable extractions. The Lean kernel has not checked any connection between Float behavior and ℝ behavior.

The Python oracle (SLICE-OL-15) passed 7/7 fixtures. This confirms the Python implementation matches hand-computed values; it does not prove the implementation is correct relative to the Lean theorems.

**Implementation risk:** Medium for current campaign (no Float correctness claims are made). High for any future work that attempts to use the Float oracle as a verified component or to derive Float-level guarantees from the exact theorems.

**Proof impact on current campaign:** None — no existing theorem depends on Float/ℝ agreement.

**Can current proofs proceed?** Yes — the separation is clean. The Float oracle and exact-real layer are independent artifacts with documented boundaries.

**Future Float bridging:**
- Status: Deferred — not part of the current campaign.
- Risk: High. A bridging theorem would require IEEE 754 rounding error bounds, which are not in scope for an exact-real Lean 4 proof campaign using Mathlib.
- If attempted: requires a new LAPS campaign with its own proof capsule, proof plan, and clear scope contract. Must not collapse the exact-real and Float layers.

**Proposed resolution:** No resolution in the current campaign. Document the separation and maintain the `⚠ FLOAT APPROXIMATION ONLY` warning in `ExecutableSemanticOracle.lean`. Any future Float campaign must be authorized separately.

---

## Summary Table

| ID | Title | Status | Proof Impact | Can Proceed? |
|----|-------|--------|--------------|--------------|
| AMB-OL-001 | Version mismatch | Unresolved | Low | Yes |
| AMB-OL-002 | ϵ′_d sign relationship | Resolved — NOT_AN_AMBIGUITY | None | Yes, spec is self-consistent throughout |
| AMB-OL-003 | Eq (8) drops ΔC + ΔP | Unresolved | HIGH | Assumption-gated |
| AMB-OL-004 | Diagonal U notation | Resolved — NOTATIONAL | None | Yes, component form correct |
| AMB-OL-005 | Radial coeff units | Unresolved | Low | Yes, with unit assumption |
| AMB-OL-006 | Decentering coeff units | Unresolved | Medium | Yes, with unit assumption |
| AMB-OL-007 | Denominator nonzero | Unresolved | HIGH | Yes, as explicit precondition |
| AMB-OL-008 | FOV/proj equivalence conditions | Unresolved | Medium | Partial |
| AMB-OL-009 | Asymmetric ΔC/ΔP in overscan | Unresolved | Medium | Scoped only |
| AMB-OL-010 | U^{−1} exact vs numerical | Partially resolved (2026-05-24) | Medium — left-inverse substantially proved; surjectivity open | Left-inverse yes; right-inverse blocked |
| AMB-OL-011 | Aperture normative? | Resolved: NOT normative | — | Defer |
| AMB-OL-012 | Overscan appendix normative? | Resolved: informative | Low | Advisory only |
| AMB-OL-013 | Default p₁, p₂ = 0 | Unresolved | Low | Yes, with assumption |
| AMB-OL-014 | U argument frame | Resolved — PROOF_ENGINEERING_ONLY | None | Yes |
| AMB-OL-015 | Which Ω for equivalence | Unresolved | Medium | Separately per form |
| AMB-OL-016 | Float oracle semantic divergence | Open — deferred | None (current); High (future Float campaign) | Yes — layers independent |
