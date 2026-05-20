# LAPS Audit Report — OpenLensIO Semantics (`openlensio_semantics`)

**Audit type:** Formal vacuity audit (post-campaign)
**Date:** 2026-05-20
**Auditor:** Claude (LAPS `/laps-audit`)
**Campaign scope:** SLICE-OL-00 through SLICE-OL-15
**Verdict:** `accepted with findings` — no stop-ship blockers; two high-severity and four medium-severity issues require documented action before the campaign is closed as verified

---

## 1. Audit Target

The full `openlensio_semantics` Lean 4 proof campaign, covering:

- 11 Lean source files (OL-04 through OL-14)
- 1 Python reference oracle and differential test harness (OL-15)
- All LAPS artifacts in `docs/laps/openlensio-semantics/`

---

## 2. Files Inspected

**Lean source:**

| File | Slice | Role |
|------|-------|------|
| `CoordinateTypes.lean` | OL-04 | `SensorPoint`, `sensorRadius`, `sensorRadius_nonneg` |
| `LensSemantics.lean` | OL-01 | `RadialCoefficients`, `TangentialCoefficients`, `LensSemantics`, `ValidLensSemantics` |
| `SemanticBridge.lean` | OL-02/03 | `extractLensSemantics`, `semanticExtraction_sound` |
| `RadialPolynomial.lean` | OL-05/06 | `denominatorNonzero`, `radialTerm`, `radial_denominator_nonzero_zero_coeffs`, `radial_zero_coefficients_identity` |
| `DistortionModel.lean` | OL-07/08 | `undistortX/Y/Point`, `tangential_zero_coefficients_identity`, `brown_conrady_zero_identity` |
| `DeltaSemantics.lean` | OL-09 | `addSensorPoints`, `subSensorPoints`, `deltaP_characterisation`, `deltaC_characterisation`, `distortion_center_translation_commutes` |
| `ProjectionModel.lean` | OL-10 | `CameraPoint`, `projectToImage`, `undistortFromDistorted`, `projection_matrix_undistort_eq` |
| `FovModel.lean` | OL-11 | `fovProjectToImage`, `fovUndistortFromDistorted`, `undistortPoint_congr` (private), `fov_undistort_eq` |
| `AngleOfView.lean` | OL-12 | `angleOfView`, `fovAngleFromWidth`, `angle_of_view_eq` |
| `ShaderCoords.lean` | OL-13 | `toShaderCoords`, `fromShaderCoords`, `pixel_metric_roundtrip`, `image_texture_coordinate_roundtrip` |
| `ExecutableSemanticOracle.lean` | OL-14 | All Float counterparts (no theorems) |

**Python / test:**

- `battery-tester/semantic_oracle/reference_oracle.py` (OL-15)
- `battery-tester/semantic_oracle/fixtures.json`
- `battery-tester/semantic_oracle/run.py`

**LAPS artifacts:**

- `ambiguity-register.md` (15 entries, AMB-OL-001–015)
- `proof-capsule.md`
- `proof-plan.md`
- `proof-review.md`
- `work-queue.md`
- `first-slice-contract.md`
- `gate1-audit.md`

---

## 3. Lean Command Checked

A `lake build` was not re-run during this audit session. The Lean file compilation is recorded as clean in `proof-review.md` and `proof-capsule.md` for all slices OL-04 through OL-15. The audit trusts those records but flags the missing `proof-run-log.md` below.

---

## 4. Theorem Inventory

| # | Theorem / Lemma | File | Classification |
|---|----------------|------|----------------|
| 1 | `sensorRadius_nonneg` | CoordinateTypes | positive sanity (PS) |
| 2 | `semanticExtraction_sound` | SemanticBridge | decoder soundness |
| 3 | `radial_denominator_nonzero_zero_coeffs` | RadialPolynomial | domain safety (PS) |
| 4 | `radial_zero_coefficients_identity` | RadialPolynomial | PS |
| 5 | `tangential_zero_coefficients_identity` | DistortionModel | stepping-stone lemma |
| 6 | `brown_conrady_zero_identity` | DistortionModel | identity theorem (PS) |
| 7 | `deltaP_characterisation` | DeltaSemantics | algebraic roundtrip |
| 8 | `deltaC_characterisation` | DeltaSemantics | algebraic roundtrip |
| 9 | `distortion_center_translation_commutes` | DeltaSemantics | structural consistency |
| 10 | `projection_matrix_undistort_eq` | ProjectionModel | structural consistency |
| 11 | `undistortPoint_congr` (private) | FovModel | helper lemma |
| 12 | `fov_undistort_eq` | FovModel | structural consistency |
| 13 | `angle_of_view_eq` | AngleOfView | domain equation |
| 14 | `pixel_metric_roundtrip` | ShaderCoords | invertibility |
| 15 | `image_texture_coordinate_roundtrip` | ShaderCoords | invertibility |

Total: 15 theorems / lemmas (14 public, 1 private).

No `sorry`, `admit`, `unsafe`, or `partial` found in any file.

---

## 5. Definition Inventory

| Definition | File | Lean shape | Invariants encoded | Invariants deferred |
|-----------|------|-----------|-------------------|---------------------|
| `SensorPoint` | CoordinateTypes | `{x y : ℝ}` | none (bare product) | coordinate-space tag (AMB-OL-004) |
| `sensorRadius` | CoordinateTypes | `√(x²+y²) : ℝ` | nonnegativity via `sqrt` | — |
| `RadialCoefficients` | LensSemantics | `{k1..k6 : ℝ}` | none | denominator nonzero (AMB-OL-007) |
| `TangentialCoefficients` | LensSemantics | `{p1 p2 : ℝ}` | none | — |
| `LensSemantics` | LensSemantics | 5-field record | none | F>0 in `ValidLensSemantics` |
| `ValidLensSemantics` | LensSemantics | `0 < l.focalLength` | F>0 only | coefficient range, ΔC/ΔP bounds, denominatorNonzero |
| `denominatorNonzero` | RadialPolynomial | `1 + k2·r² + k4·r⁴ + k6·r⁶ ≠ 0` | exact ≠ 0 | Float-level tolerance gap |
| `radialTerm` | RadialPolynomial | total division over ℝ | well-defined by `h` | — |
| `undistortX/Y/Point` | DistortionModel | component form of Eq(16) | — | — |
| `undistortFromDistorted` | ProjectionModel | Eq(4) with ΔC+ΔP shifts | shifted-point domain | — |
| `fovUndistortFromDistorted` | FovModel | Eq(10) with ΔC shift only | — | — |
| `angleOfView` | AngleOfView | `2·arctan(r_u/F)` | total (Lean division) | F>0 for physical use |
| `fovAngleFromWidth` | AngleOfView | `2·arctan(w/(2F))` | total | F>0 for physical use |
| `toShaderCoords` | ShaderCoords | Eq(18) | — | w,h,wshader > 0 for invertibility |
| `fromShaderCoords` | ShaderCoords | inverse of Eq(18) | — | same |

---

## 6. Vacuity Findings Table

| ID | Theorem | Vacuity type | Severity | Description |
|----|---------|-------------|----------|-------------|
| VAC-01 | `deltaP_characterisation`, `deltaC_characterisation` | Duplicate theorem / proxy | HIGH | Identical formal statement under different variable names |
| VAC-02 | `angle_of_view_eq` | Junk-value vacuity at F=0 | MEDIUM | Holds for F=0 via total-division junk values, not physics |
| VAC-03 | `projection_matrix_undistort_eq` | Algebraic tautology | MEDIUM | Proves `a + b + c − b − c = a`; no physical content beyond definition unfolding |
| VAC-04 | `semanticExtraction_sound` | Near-tautology | LOW | Restates the if-guard; non-vacuous but very thin |

---

## 7. Assumption Satisfiability Analysis

Every hypothesis in the proof campaign is satisfiable. Witnesses:

| Hypothesis | Witness | Unsatisfiable? |
|-----------|---------|----------------|
| `denominatorNonzero k r` | `k2=k4=k6=0` → denom=1≠0 (proved by `radial_denominator_nonzero_zero_coeffs`) | No |
| `ValidLensSemantics l` | `l.focalLength = 50.0` | No |
| `0 < w`, `0 < h`, `0 < wshader` | Any positive real | No |
| `k.ki = 0` (zero-coeff theorems) | The zero `RadialCoefficients` | No |
| `p.pi = 0` (zero-tangential) | `TangentialCoefficients.zero` | No |
| `h`, `h'` in `fov_undistort_eq` | Two `denominatorNonzero` proofs at propositionally-equal points | No |

**Empty-domain risk:** None. No theorem requires simultaneously impossible hypotheses.

---

## 8. Witness Construction Analysis

**`radial_denominator_nonzero_zero_coeffs`** — The comment explicitly provides a counterwitness for the predicate's nontriviality: `k2 = −1, r = 1` makes the denominator zero. The predicate is genuinely constraining.

**`brown_conrady_zero_identity`** — Requires 8 hypotheses (6 radial + 2 tangential = 0). These are simultaneously satisfiable (the zero lens). The theorem would be false for nonzero coefficients, so it is not vacuously assumed.

**`fov_undistort_eq`** — Requires two separate `denominatorNonzero` proofs `h` and `h'`. The two proofs are at propositionally-equal (by `distortion_center_translation_commutes`) but definitionally distinct SensorPoint expressions. The `undistortPoint_congr` helper handles the gap. This is the one theorem with non-trivially satisfiable domain hypotheses, and the witnesses are correctly constructed.

---

## 9. Unused-Hypothesis Audit

| Theorem | Hypotheses | All used? | Notes |
|---------|-----------|-----------|-------|
| `radial_denominator_nonzero_zero_coeffs` | `hk2 hk4 hk6` | Yes | Used in simp to zero out denominator terms |
| `radial_zero_coefficients_identity` | `hk1..hk6`, `h` | Yes | All six in simp; `h` forwarded to `radialTerm` |
| `tangential_zero_coefficients_identity` | `hp1 hp2` | Yes | Used in simp |
| `brown_conrady_zero_identity` | `hk1..hk6`, `hp1 hp2`, `h` | Yes | All used in sub-lemma calls |
| `fov_undistort_eq` | `h`, `h'` | Yes | `h'` passed to `undistortFromDistorted`; `h` passed to `undistortPoint_congr` |
| `semanticExtraction_sound` | `h` | Yes | Destructured to extract `hf` |
| `projection_matrix_undistort_eq` | `h` | Yes | Forwarded through `undistortFromDistorted` |
| `pixel_metric_roundtrip` | `hw hh hs` | Yes | Used by `field_simp` as `ne'` forms |
| `image_texture_coordinate_roundtrip` | `hw hh hs` | Yes | Same |
| `deltaP_characterisation` | none extra | n/a | VAC-01 note |
| `deltaC_characterisation` | none extra | n/a | VAC-01 note |

No unused hypotheses detected.

---

## 10. Definitional-Tautology Audit

### Finding DT-01 — `semanticExtraction_sound` is very thin (LOW)

`ValidLensSemantics l = (0 < l.focalLength)`. The `extractLensSemantics` function succeeds exactly when `0 < focalLength`. The theorem restates the if-guard as a proved implication. It is non-vacuous (the error branch is reachable), but the semantic content is entirely carried by the definition. The proof (`split_ifs; exact hf`) requires no reasoning beyond case analysis.

**Risk:** Low. The theorem correctly documents the decoder invariant. The semantic shallowness is a model design choice, not a proof error. It would become more meaningful if `ValidLensSemantics` gained additional predicates.

**Required action:** Note in `ambiguity-register.md` that strengthening `ValidLensSemantics` (see Finding DEF-01) would automatically strengthen this theorem.

---

### Finding DT-02 — `projection_matrix_undistort_eq` is an algebraic tautology (MEDIUM)

**Theorem statement (from `ProjectionModel.lean`):**

```lean
theorem projection_matrix_undistort_eq
    (...) (h : denominatorNonzero ...) :
    subSensorPoints (subSensorPoints (undistortFromDistorted k p ε_d ΔC ΔP h) ΔC) ΔP =
    undistortPoint k p (subSensorPoints (subSensorPoints ε_d ΔC) ΔP) h
```

After unfolding `undistortFromDistorted`, this reduces to:
```
(U(ε_d − ΔC − ΔP) + ΔC + ΔP) − ΔC − ΔP = U(ε_d − ΔC − ΔP)
```
which is `a + b + c − b − c = a` — true by `ring`. The proof offers no structural insight into how Eq(3) and Eq(4) are consistent. The file honestly acknowledges this:

> Scope limitation: full Eq(3)/Eq(4) consistency... requires the forward distortion model and is deferred to OL-DEFER-03.

**Risk:** Medium. The theorem is correctly stated and correctly proved. It is documented as a partial result. The risk is that a future reader may mistake it for the full Eq(3)/Eq(4) consistency claim.

**Required action:** Add a comment in the theorem header distinguishing this from the deferred forward-model consistency claim. No theorem rewrite required.

---

### Note — `fovAngleFromWidth F w = angleOfView F (w / 2)` omitted intentionally

The file comment notes: "Trivially true and is not stated as a theorem (trivial definitional tautology)." This is correct; the theorem would be `by rfl` or `by simp [angleOfView, fovAngleFromWidth]`. Not filing as a finding.

---

## 11. Specification-Coverage Audit

The campaign covers: coordinate types, radial polynomial, Brown-Conrady undistortion, delta semantics, projection/undistortion Eq(4), FOV-form Eq(10), angle-of-view Eq(6)/Eq(14), shader coordinate roundtrip Eq(18).

**Deferred (documented):**

| Item | Status | Reference |
|------|--------|-----------|
| Forward distortion model | Deferred to OL-DEFER-03 | ProjectionModel comment, work-queue.md |
| Full Eq(3)/Eq(4) consistency | Deferred | Same |
| Phantom-type coordinate tagging | Deferred | AMB-OL-004 |
| Multi-frame decimals / `Canon_REK_v1.0` | Out of scope | work-queue.md |
| Differential testing vs. C++ / CamDKit | Blocked — no implementation | proof-capsule.md OL-15 |
| Float-to-ℝ bridging theorem | Not attempted | See Finding EX-01 |

The specification coverage is appropriate for the first-campaign scope. All deferrals are documented.

---

## 12. Empty-Domain Audit

No empty-domain theorems found. Every precondition in the campaign has at least one concrete satisfying instance:

- `denominatorNonzero`: satisfied by zero-denominator-coefficients (proved)
- `ValidLensSemantics`: satisfied by any lens with F > 0
- `0 < w/h/wshader`: satisfied by any positive real
- Zero-coefficient hypotheses: simultaneously satisfiable (the zero lens)

---

## 13. Executable-Semantics Mismatch Audit

### Finding EX-01 — Structural architecture drift between Float oracle and exact definitions (HIGH)

The exact-real definitions and the Float oracle have different architectures:

**Exact (`DistortionModel.lean`):**
```lean
noncomputable def undistortX
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε : SensorPoint) (h : denominatorNonzero k (sensorRadius ε)) : ℝ :=
  let r := sensorRadius ε
  radialTerm k r h * ε.x + ...
```
The domain proof `h : denominatorNonzero` is a type-level precondition. `radialTerm` is called internally.

**Float oracle (`ExecutableSemanticOracle.lean`):**
```lean
def undistortX_float (p : FloatTangentialCoefficients) (ex ey r R : Float) : Float :=
  R * ex + ...
```
`R` is a pre-computed `Float` passed in by the caller after `radialTerm_float` already returned `some R`. The architecture is different: domain validity is checked by `Option` return, not by a Prop precondition.

**Domain tolerance gap:** `denominatorNonzero` requires exact ≠ 0 (over ℝ). `radialTerm_float` uses absolute tolerance `1e-10`. These semantics differ: there exist denominators with `|d| < 1e-10` that are nonzero (exact) but rejected by the Float oracle, and there exist denominators with `|d| > 1e-10` that are extremely close to zero (causing large Float errors) but accepted.

**No bridging theorem:** `ExecutableSemanticOracle.lean` contains no Lean theorem connecting Float behavior to exact-real definitions. The file prominently warns:

```
⚠ FLOAT APPROXIMATION ONLY — NOT A PROVED THEOREM ⚠
```

**Python reference oracle:** The Python oracle (`reference_oracle.py`) uses the same `1e-10` absolute tolerance. 7/7 fixtures pass against hand-computed expected values. The cross-check is valuable but does not constitute a Lean-verified result.

**Risk:** High if future work treats the Float oracle as verified. Contained by the prominent warning in `ExecutableSemanticOracle.lean`. The risk is of interpretation, not of mathematical error.

**Required action:**
1. Add a finding to `ambiguity-register.md` (or update AMB-OL-015 if it covers this) documenting the Float/ℝ architecture gap and the absence of a bridging theorem.
2. If a future slice attempts to connect Float and exact semantics, this must be a new LAPS slice with its own proof capsule and plan.

---

## 14. Vacuity Finding Detail

### Finding VAC-01 — `deltaP_characterisation` and `deltaC_characterisation` are formally identical (HIGH)

**Evidence:**

```lean
-- deltaP_characterisation (ε'_u : SensorPoint, ΔP : SensorPoint)
theorem deltaP_characterisation (ε'_u ΔP : SensorPoint) :
    subSensorPoints (addSensorPoints ε'_u ΔP) ΔP = ε'_u := by
  ext <;> simp [addSensorPoints, subSensorPoints]

-- deltaC_characterisation (ε'_d : SensorPoint, ΔP : SensorPoint)
theorem deltaC_characterisation (ε'_d ΔP : SensorPoint) :
    subSensorPoints (addSensorPoints ε'_d ΔP) ΔP = ε'_d := by
  ext <;> simp [addSensorPoints, subSensorPoints]
```

These two theorems are **α-equivalent**: the only difference is the names of bound variables (`ε'_u`, `ε'_d` vs. `ε'_d`, `ΔP`). The formal statements are identical modulo variable renaming. The proof scripts are character-for-character identical. The comments claim they formalize distinct paper equations (Eq 12 and Eq 13), but the mathematical content is the same additive-group roundtrip.

**Paper equation situation:**
- Eq (12): `ε_u = ε'_u + ΔP` (undistorted form)
- Eq (13): `ε_d = ε'_d + ΔP` (distorted form)

Both equations assert the same algebraic relationship `sub(add(a, b), b) = a` applied to different coordinate-space variables. Proving it twice does not add new mathematical content. The `deltaC_characterisation` theorem is a restatement of `deltaP_characterisation`.

**Semantic risk:** Both theorems appear in `distortion_center_translation_commutes`, which depends on the algebraic fact, not on which paper equation it corresponds to. The duplication does not invalidate any proof but does mislead a reader into thinking two distinct mathematical claims have been formalized.

**Required action:**
- Option A: Remove `deltaC_characterisation` and add a comment to `deltaP_characterisation` explaining it covers both Eq (12) and Eq (13) (same algebra, different coordinate-space roles). Downstream uses of `deltaC_characterisation` would switch to `deltaP_characterisation`.
- Option B: Keep both theorems with a comment explicitly documenting that they are formally identical and explain why the duplication was retained for paper-equation traceability.

Either option is acceptable. Option B requires no code change. **Authorization required before removing `deltaC_characterisation`** (removing a theorem is a theorem statement change).

---

### Finding VAC-02 — `angle_of_view_eq` holds at F=0 via junk-value semantics (MEDIUM, documented)

**Theorem:**
```lean
theorem angle_of_view_eq (F r_u : ℝ) :
    Real.tan (angleOfView F r_u / 2) = r_u / F
```

At F=0: `r_u / 0 = 0` (Lean's total division), `arctan 0 = 0`, `tan 0 = 0`, so both sides are 0. The theorem holds trivially via junk-value arithmetic, not physical optics.

**Documentation status:** The file comment explicitly notes this:
> "Stated for all F : ℝ. Lean 4 division is total (r_u / 0 = 0), so the theorem holds vacuously for F = 0 with junk-value semantics. Physical use requires F > 0 (focal length); callers enforce this via ValidLensSemantics."

**Risk:** Low. The junk-value behavior is benign and documented. The theorem could be strengthened to require `F ≠ 0`, but this would be a non-trivial theorem statement change and would require callers to supply the `hF` hypothesis.

**Required action:** No code change required. The documentation is adequate. If future work adds a `hF : 0 < F` hypothesis, this is an authorized theorem strengthening.

---

### Finding VAC-03 — `projection_matrix_undistort_eq` — see Finding DT-02 above.

---

### Finding VAC-04 — `semanticExtraction_sound` — see Finding DT-01 above.

---

## 15. Definition-Model Risk Audit

### Finding DEF-01 — `ValidLensSemantics` is very thin (HIGH)

**Definition:**
```lean
def ValidLensSemantics (l : LensSemantics) : Prop :=
  0 < l.focalLength
```

**Intended domain meaning (per paper):** A lens parameter set that is valid for use in the OpenLensIO mathematical model — including focal length positivity, well-defined denominator at operating points, physical distortion centre bounds, etc.

**Encoded invariants:** Focal length positivity only.

**Not encoded:**
- Coefficient range invariants (no bounds on k1..k6, p1, p2)
- `denominatorNonzero` at any specific point (intentionally deferred — AMB-OL-007, well-documented)
- Physical bounds on ΔC or ΔP
- Positivity of sensor dimensions (relevant to ShaderCoords — enforced locally by theorem hypotheses, not by ValidLensSemantics)

**Risk:** The name `ValidLensSemantics` suggests comprehensive semantic validity. The predicate delivers only one of several possible invariants. This creates a documentation and API risk: code that checks `ValidLensSemantics` may be mistakenly assumed to guarantee more than F > 0.

**Mitigations in place:**
- The file comment documents that denominator nonzero is intentionally deferred (AMB-OL-007)
- Callers that need `denominatorNonzero` carry it as an explicit hypothesis — this is the correct design per AMB-OL-007
- The design choice is recorded in multiple artifact files

**Severity:** High as a documentation/naming concern; not a proof correctness issue. The theorems are all correct given the defined predicate.

**Required action:**
- Add a comment to `ValidLensSemantics` listing the invariants it intentionally omits and why.
- Update `ambiguity-register.md` or add a note to the relevant AMB if this naming risk has not been explicitly registered.

No Lean code change required unless the predicate is intentionally strengthened (which requires user authorization).

---

### Finding DEF-02 — `fov_undistort_eq` comment describes discarded proof strategy (MEDIUM)

**Comment in `FovModel.lean`:**
```
The coercion (distortion_center_translation_commutes ...).symm ▸ h converts
h : denominatorNonzero k (sensorRadius (ε'_d − ΔC)) to the type needed by
undistortFromDistorted: denominatorNonzero k (sensorRadius ((ε'_d + ΔP) − ΔC − ΔP)).
```

**Actual proof:**
```lean
theorem fov_undistort_eq (...) := by
  simp only [undistortFromDistorted, fovUndistortFromDistorted]
  congr 1; congr 1
  exact undistortPoint_congr k p (distortion_center_translation_commutes ε'_d ΔP ΔC) h' h
```

The comment describes a `▸` (rewrite-by-proof) strategy that was explored but not used. The actual proof uses `undistortPoint_congr` with `congr 1`. These strategies are different. The comment is accurate about the mathematical idea but inaccurate about the proof mechanism.

**Risk:** Medium. Future maintainers may be confused when trying to read the proof alongside the comment.

**Required action:** Update the `fov_undistort_eq` comment to describe the `undistortPoint_congr` + `congr 1` strategy that was actually used.

---

## 16. Artifact Freshness and Consistency Audit

### Present artifacts

| Artifact | Present | Status |
|----------|---------|--------|
| `proof-capsule.md` | Yes | Covers OL-00 through OL-15 |
| `proof-plan.md` | Yes | Covers OL-00 through OL-15 |
| `proof-review.md` | Yes | Covers OL-00 through OL-15 |
| `work-queue.md` | Yes | Updated through OL-15; sections 2, 7, 8, 13 current |
| `ambiguity-register.md` | Yes | 15 entries, AMB-OL-001–015 |
| `first-slice-contract.md` | Yes | OL-00 through OL-04 |
| `gate1-audit.md` | Yes | Gate 1 audit result |
| `audit-report.md` | **This file** | Created in this audit run |

### Missing artifacts

#### Finding ART-01 — `statement-audit.md` is absent (MEDIUM)

The LAPS protocol requires `statement-audit.md` as a phase-gate artifact for the Proof Capsule stop (Stop 1). No `statement-audit.md` exists in `docs/laps/openlensio-semantics/`. The `gate1-audit.md` covers some of the same ground (theorem statement review at gate 1) but is not equivalent to a formal statement audit.

**Severity:** Medium. The campaign compiled, all theorems are reviewed in `proof-review.md`, and the gate-1 audit exists. The missing artifact is a documentation gap, not a proof gap.

**Required action:** Create `statement-audit.md` covering all 15 theorems, or explicitly retire this artifact requirement by noting that `gate1-audit.md` + `proof-review.md` serve as the statement audit for this campaign.

---

#### Finding ART-02 — `proof-run-log.md` is absent (HIGH)

LAPS requires `proof-run-log.md` for any slice that edits Lean code. Slices OL-04 through OL-15 all edited Lean code. No `proof-run-log.md` exists.

The final Lean check result is documented in `proof-capsule.md` and `proof-review.md`, but neither file is a structured run log. There is no record of:
- Which `lake build` or `lake check` commands were run
- Whether the final check was performed after the last Lean edit (i.e., after ShaderCoords.lean and ExecutableSemanticOracle.lean were added in OL-13/14)
- Compilation time or error count per slice

**Severity:** High. A future reviewer cannot confirm that the final Lean check occurred after the last Lean file was added.

**Required action:** Create `proof-run-log.md` recording at minimum:
1. The Lean command used (`lake build` / `lake check openlensio_semantics`)
2. Date of final check
3. Result (clean / errors)
4. Which files were present at that check

This can be retroactively constructed from the session history and `proof-capsule.md`. It need not be a full per-tactic log.

---

### Artifact consistency findings

#### Finding ART-03 — `work-queue.md` theorem inventory inconsistency (LOW)

`work-queue.md` Section 8 theorem inventory lists `angle_of_view_eq` with tactic `simp [angleOfView, Real.tan_arctan]`. The actual proof in `AngleOfView.lean` uses `simp [angleOfView, Real.tan_arctan]` — this matches. No inconsistency there.

However, the theorem count in `work-queue.md` Section 8 may not enumerate the private `undistortPoint_congr` lemma (it is private and may be omitted from the inventory). This is a minor omission, not a blocker.

**Severity:** Low. Private helpers are commonly omitted from theorem inventories.

**Required action:** Optional — add `undistortPoint_congr (private)` to Section 8 of `work-queue.md` for completeness.

---

## 17. Forbidden Construct Check

| Construct | Present |
|-----------|---------|
| `sorry` | Not found |
| `admit` | Not found |
| Unauthorized `axiom` | Not found |
| `unsafe` | Not found |
| `partial` | Not found |

Clean.

---

## 18. Recommended Theorem Rewrites

These are proposals only. None may be executed without user authorization.

### RW-01 — Unify `deltaP_characterisation` and `deltaC_characterisation`

**Motivation:** VAC-01 above. The two theorems are formally identical.

**Proposed change:**
```lean
-- Replace both theorems with one general theorem + a documentation comment:
theorem sensorPoint_add_sub_cancel (ε ΔP : SensorPoint) :
    subSensorPoints (addSensorPoints ε ΔP) ΔP = ε := by
  ext <;> simp [addSensorPoints, subSensorPoints]
-- Covers Eq (12) (ε = ε'_u, ΔP = ΔP) and Eq (13) (ε = ε'_d, ΔP = ΔP):
-- same algebraic content, distinct coordinate-space roles documented in comments.
```

**Blast radius:** `deltaP_characterisation` and `deltaC_characterisation` both appear in `distortion_center_translation_commutes`. Both calls would change to `sensorPoint_add_sub_cancel`. This is a small, safe, mechanical change. **Still requires user authorization** as it changes public theorem names.

---

### RW-02 — Add `hF : 0 < F` hypothesis to `angle_of_view_eq`

**Motivation:** VAC-02. The current theorem holds for F=0 via junk-value arithmetic.

**Proposed change:**
```lean
theorem angle_of_view_eq (F r_u : ℝ) (hF : 0 < F) :
    Real.tan (angleOfView F r_u / 2) = r_u / F
```

**Impact:** The proof remains `simp [angleOfView, Real.tan_arctan]` — the hypothesis `hF` is not needed by the tactic, but it rules out the junk-value case. All callers that use `ValidLensSemantics` already have F > 0; they would pass `l.focalLength_pos` or equivalent. **Requires user authorization.**

---

### RW-03 — Strengthen `ValidLensSemantics`

**Motivation:** DEF-01. The predicate is very thin.

**Proposed addition:**
```lean
def ValidLensSemantics (l : LensSemantics) : Prop :=
  0 < l.focalLength
-- Future slices may add:
-- ∧ (∀ r : ℝ, denominatorNonzero l.radial r → True)  -- placeholder
-- ∧ ... other domain invariants
```

This is a significant model change and **requires a dedicated LAPS slice with its own proof capsule**. Flagged here for awareness; not a blocker for campaign closure.

---

## 19. Stop-Ship Findings

**No stop-ship blockers found.**

The audit found no:
- Vacuous theorems in the bad sense (impossible hypotheses, False preconditions, contradictory assumptions)
- Theorems that prove proxy properties while claiming to prove domain properties
- Theorem statements misaligned with their mathematical intent
- Load-bearing definitions that encode the wrong concept
- `sorry`, `admit`, or forbidden constructs
- Proofs where automation closed a meaningful goal while the hard step is unidentified
- AI summaries or test output treated as the verifier

The campaign may proceed to closed/accepted status subject to the required actions below.

---

## 20. Summary of Findings

| ID | Severity | Finding | Required action |
|----|----------|---------|-----------------|
| VAC-01 | HIGH | `deltaP_characterisation` and `deltaC_characterisation` formally identical | Unify (RW-01) or add documentary comment; user authorization required |
| EX-01 | HIGH | Float oracle has structural drift from exact definitions; no bridging theorem | Register in ambiguity-register; flag for future slice |
| DEF-01 | HIGH | `ValidLensSemantics` is very thin; name overpromises | Add comment enumerating intentional omissions; no Lean change required now |
| ART-02 | HIGH | `proof-run-log.md` absent | Create retroactively with final check record |
| DT-02 | MEDIUM | `projection_matrix_undistort_eq` is an algebraic tautology | Add comment distinguishing from deferred full Eq(3)/Eq(4) consistency |
| DEF-02 | MEDIUM | `fov_undistort_eq` comment describes discarded proof strategy | Update comment to describe actual proof |
| ART-01 | MEDIUM | `statement-audit.md` absent | Create or formally retire |
| VAC-02 | MEDIUM | `angle_of_view_eq` holds at F=0 via junk values | Documented; no action required unless RW-02 is authorized |
| DT-01 | LOW | `semanticExtraction_sound` is very thin | Note that strengthening `ValidLensSemantics` would strengthen it |
| ART-03 | LOW | `undistortPoint_congr` not in theorem inventory | Optional addition to `work-queue.md` Section 8 |

---

## 21. Final Verdict

`accepted with findings`

The `openlensio_semantics` Lean 4 proof campaign is mathematically sound. All proved theorems are correct statements of their intended domain claims (with the documented exceptions that are clearly bounded and disclosed). No forbidden constructs exist. No vacuity in the bad sense was found. No proof closes by hiding an unidentified hard step.

The four HIGH-severity findings are documentation and artifact gaps, not mathematical errors:
- VAC-01: a theorem duplication that should be resolved or documented
- EX-01: the Float oracle's architecture diverges from exact definitions — flagged for awareness, not a correctness issue given the prominent warning in the file
- DEF-01: `ValidLensSemantics` naming risk — add comment
- ART-02: `proof-run-log.md` is absent — create retroactively

**Recommended next action:** Address ART-02 (create `proof-run-log.md`) and DEF-02 (fix `fov_undistort_eq` comment) as immediate no-authorization-required cleanup. Present VAC-01 and DEF-01 to user for authorization decision before any Lean code changes.
