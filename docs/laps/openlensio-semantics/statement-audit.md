---
name: openlensio-semantics-statement-audit
description: Theorem statement audit for openlensio_semantics — classifies all public theorems, scope limitations, and deferred obligations
metadata:
  type: reference
---

# Statement Audit — `openlensio_semantics`

Campaign: SLICE-OL-00 through OL-15
Date: 2026-05-20
Status: Complete — all 14 public theorems audited

This artifact records the intended semantic meaning of each theorem, compares it to the actual Lean statement, identifies scope limitations, and classifies the theorem type. It was created during the closeout pass following the vacuity audit (finding ART-01).

---

## Classification Key

| Class | Meaning |
|-------|---------|
| **substantive** | Proves a non-trivial domain claim about the lens model |
| **algebraic** | Proves a polynomial / arithmetic identity, usually by `ring` |
| **structural** | Proves consistency between two definitional forms without full equivalence |
| **stepping-stone** | Proved to support a later theorem; not independently meaningful |
| **identity** | Proves that a function reduces to the identity under degenerate inputs |
| **partial** | The theorem proves a weaker claim than what full correctness would require |
| **domain-safety** | Proves a domain predicate holds under specified conditions |

Multiple classifications are allowed.

---

## T-01 — `sensorRadius_nonneg`

**File:** `CoordinateTypes.lean`
**Lean statement:**
```lean
theorem sensorRadius_nonneg (p : SensorPoint) : 0 ≤ sensorRadius p
```
**Intended meaning:** The sensor radius `r = √(ε_x² + ε_y²)` is always nonneg­ative. Required for `denominatorNonzero` reasoning and for downstream theorems that use `r^2 ≥ 0`.
**Statement match:** Exact.
**Proof:** `Real.sqrt_nonneg _` — one-liner, closed by Mathlib.
**Classification:** domain-safety, stepping-stone
**Scope limitations:** None — this is a total property of `Real.sqrt`.
**Deferred obligations:** None.

---

## T-02 — `semanticExtraction_sound`

**File:** `SemanticBridge.lean`
**Lean statement:**
```lean
theorem semanticExtraction_sound
    (focalLength : ℝ) (k1 k2 k3 k4 k5 k6 : ℝ) (p1 p2 : ℝ)
    (dcx dcy dpx dpy : ℝ) (s : LensSemantics)
    (h : extractLensSemantics focalLength k1 k2 k3 k4 k5 k6 p1 p2 dcx dcy dpx dpy = .ok s) :
    ValidLensSemantics s
```
**Intended meaning:** A successful semantic extraction guarantees the result satisfies `ValidLensSemantics`. Caller confidence: if `extractLensSemantics` returns `.ok`, the lens is safe to use in theorem contexts requiring a valid lens.
**Statement match:** Matches intent within the scope of `ValidLensSemantics` (which is F > 0 only; see DEF-01).
**Proof:** `split_ifs` on the if-guard; positive branch `exact hf`; negative branch contradiction.
**Classification:** substantive, partial
**Scope limitations:** `ValidLensSemantics` only guarantees `focalLength > 0`. No guarantee on coefficient ranges, denominator validity at any point, or physical calibration bounds. See T-02 scope note and DEF-01 in `audit-report.md`.
**Deferred obligations:**
- If `ValidLensSemantics` is strengthened in a future slice, this theorem's proof obligation grows accordingly.

---

## T-03 — `radial_denominator_nonzero_zero_coeffs`

**File:** `RadialPolynomial.lean`
**Lean statement:**
```lean
theorem radial_denominator_nonzero_zero_coeffs
    (k : RadialCoefficients) (r : ℝ)
    (hk2 : k.k2 = 0) (hk4 : k.k4 = 0) (hk6 : k.k6 = 0) :
    denominatorNonzero k r
```
**Intended meaning:** The canonical domain-safe case: when all denominator coefficients (k2, k4, k6) are zero, the denominator is 1 ≠ 0 for all r. Provides a concrete witness that `denominatorNonzero` is satisfiable.
**Statement match:** Exact.
**Proof:** `simp [denominatorNonzero, hk2, hk4, hk6]` — reduces denominator to 1, then `1 ≠ 0` by norm.
**Classification:** domain-safety, stepping-stone
**Scope limitations:** Only covers zero denominator coefficients. General denominator positivity (for nonzero coefficients at specific r values) is not proved and not required by the campaign.
**Non-vacuity witness documented:** k2 = −1, r = 1 → denominator = 0 → `denominatorNonzero` fails. The predicate is genuinely constraining.
**Deferred obligations:** None for this campaign.

---

## T-04 — `radial_zero_coefficients_identity`

**File:** `RadialPolynomial.lean`
**Lean statement:**
```lean
theorem radial_zero_coefficients_identity
    (k : RadialCoefficients) (r : ℝ)
    (hk1 : k.k1 = 0) (hk2 : k.k2 = 0) (hk3 : k.k3 = 0)
    (hk4 : k.k4 = 0) (hk5 : k.k5 = 0) (hk6 : k.k6 = 0)
    (h : denominatorNonzero k r) :
    radialTerm k r h = 1
```
**Intended meaning:** A lens with all-zero radial coefficients has no radial distortion factor (R = 1). This is the zero-distortion identity for the radial polynomial (§4.1).
**Statement match:** Exact.
**Proof:** `simp only [radialTerm, ...]` zeros out all coefficient terms; `norm_num` closes `1/1 = 1`.
**Classification:** identity, stepping-stone
**Scope limitations:** Requires all six coefficients to be zero. Partial-zero cases (e.g., k1=k3=k5=0 only) are not proved.
**Deferred obligations:** None for this campaign.

---

## T-05 — `tangential_zero_coefficients_identity`

**File:** `DistortionModel.lean`
**Lean statement:**
```lean
theorem tangential_zero_coefficients_identity
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε : SensorPoint) (h : denominatorNonzero k (sensorRadius ε))
    (hp1 : p.p1 = 0) (hp2 : p.p2 = 0) :
    undistortX k p ε h = radialTerm k (sensorRadius ε) h * ε.x
```
**Intended meaning:** With zero tangential coefficients, the x-component of U reduces to R·ε_x. This is a stepping stone to `brown_conrady_zero_identity`.
**Statement match:** Exact — proves only the x-component, not the full point.
**Proof:** `simp only [undistortX, hp1, hp2, ...]` cancels tangential terms.
**Classification:** stepping-stone, identity (partial)
**Scope limitations:** x-component only. The y-component is handled implicitly in `brown_conrady_zero_identity` by simp.
**Deferred obligations:** None.

---

## T-06 — `brown_conrady_zero_identity`

**File:** `DistortionModel.lean`
**Lean statement:**
```lean
theorem brown_conrady_zero_identity
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε : SensorPoint) (h : denominatorNonzero k (sensorRadius ε))
    (hk1..hk6 : k.ki = 0) (hp1 : p.p1 = 0) (hp2 : p.p2 = 0) :
    undistortPoint k p ε h = ε
```
**Intended meaning:** With all eight distortion coefficients zero, U is the identity function (U(ε) = ε). This is the zero-distortion theorem: a lens with no distortion parameters passes coordinates through unchanged.
**Statement match:** Exact.
**Proof:** Chain T-04 (R=1) + T-05 (Ux = ε.x) + simp for Uy; close by `SensorPoint.ext`.
**Classification:** substantive, identity
**Scope limitations:** Requires all 8 coefficients to be zero. General lenses (arbitrary k, p) are handled by the full `undistortPoint` definition; this proves only the zero case.
**Deferred obligations:** None.

---

## T-07 — `deltaP_characterisation`

**File:** `DeltaSemantics.lean`
**Lean statement:**
```lean
theorem deltaP_characterisation (ε'_u ΔP : SensorPoint) :
    subSensorPoints (addSensorPoints ε'_u ΔP) ΔP = ε'_u
```
**Intended meaning:** Formal statement of §3 Eq (12): adding ΔP and then subtracting it returns the original undistorted coordinate ε'_u. Documents the algebraic content of the ε_u = ε'_u + ΔP relationship.

**⚠ Formal note (VAC-01):** This theorem is formally α-equivalent to `deltaC_characterisation`. The two theorems prove the same algebraic fact `sub(add(a,b),b) = a` with different bound variable names. Both are retained for paper-equation traceability (Eq 12 vs Eq 13), not for mathematical distinctness. See T-08.

**Proof:** `ext <;> simp [addSensorPoints, subSensorPoints]`
**Classification:** algebraic, structural (partial — encodes direction of relationship only)
**Scope limitations:** Proves the roundtrip direction only. Does not prove ΔP is the unique such offset.
**Deferred obligations:** None.

---

## T-08 — `deltaC_characterisation`

**File:** `DeltaSemantics.lean`
**Lean statement:**
```lean
theorem deltaC_characterisation (ε'_d ΔP : SensorPoint) :
    subSensorPoints (addSensorPoints ε'_d ΔP) ΔP = ε'_d
```
**Intended meaning:** Formal statement of §3 Eq (13): adding ΔP and then subtracting it returns the original distorted coordinate ε'_d. Documents the algebraic content of the ε_d = ε'_d + ΔP relationship.

**⚠ Formal note (VAC-01):** This theorem is formally α-equivalent to `deltaP_characterisation`. The theorems have identical proof scripts and identical formal statements modulo variable names. The duplication is intentional: both paper equations (Eq 12 and Eq 13) make the same algebraic claim about different coordinate-space variables (undistorted vs. distorted). The coordinate-role distinction is interpretive, not algebraic. A single theorem would suffice formally; both are retained for traceability.

**Proof:** `ext <;> simp [addSensorPoints, subSensorPoints]`
**Classification:** algebraic, structural (partial — same as T-07)
**Scope limitations:** Same as T-07. Distinct coordinate-space role (distorted coordinates) is a documentation distinction, not a formal one.
**Deferred obligations:** None.

---

## T-09 — `distortion_center_translation_commutes`

**File:** `DeltaSemantics.lean`
**Lean statement:**
```lean
theorem distortion_center_translation_commutes (ε'_d ΔP ΔC : SensorPoint) :
    subSensorPoints (subSensorPoints (addSensorPoints ε'_d ΔP) ΔC) ΔP =
    subSensorPoints ε'_d ΔC
```
**Intended meaning:** The ΔP terms cancel when composing Eq(13) and the inner shift of Eq(4)/(10): `(ε'_d + ΔP) − ΔC − ΔP = ε'_d − ΔC`. This is the key algebraic fact connecting Eq(4) and Eq(10): both feed U the same distortion-centred argument.
**Statement match:** Exact. This is the load-bearing structural lemma for `fov_undistort_eq`.
**Proof:** `ext <;> simp [...] <;> ring`
**Classification:** algebraic, structural, stepping-stone
**Scope limitations:** Proves only the argument-to-U equality. Does not prove the output of U is equal (that is `fov_undistort_eq`'s job). Does not prove any physical property of ΔC or ΔP.
**Deferred obligations:** None.

---

## T-10 — `projection_matrix_undistort_eq`

**File:** `ProjectionModel.lean`
**Lean statement:**
```lean
theorem projection_matrix_undistort_eq
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε_d ΔC ΔP : SensorPoint)
    (h : denominatorNonzero k (sensorRadius (subSensorPoints (subSensorPoints ε_d ΔC) ΔP))) :
    subSensorPoints (subSensorPoints (undistortFromDistorted k p ε_d ΔC ΔP h) ΔC) ΔP =
    undistortPoint k p (subSensorPoints (subSensorPoints ε_d ΔC) ΔP) h
```
**Intended meaning:** Removing the ΔC+ΔP offset from the output of `undistortFromDistorted` recovers the raw `undistortPoint` output. Documents that `undistortFromDistorted` is structured as `U(...) + ΔC + ΔP`, so stripping the offset back yields U.

**⚠ Scope limitation (DT-02):** This theorem proves algebraic offset-cancellation consistency within Eq(4) only. It does NOT prove full Eq(3)/Eq(4) forward/inverse equivalence. In particular:
- It does not relate `projectToImage` (Eq 3) to `undistortFromDistorted` (Eq 4).
- It does not prove that U is invertible or that forward distortion composes correctly with undistortion.
- Full forward/inverse equivalence requires the forward distortion model (OL-DEFER-03), which is not part of this campaign.

**Proof:** `ext <;> simp [undistortFromDistorted, addSensorPoints, subSensorPoints] <;> ring`
After unfolding, the goal reduces to `a + b + c − b − c = a`, closed by `ring`.
**Classification:** algebraic, structural, **partial**
**Deferred obligations:**
- Full Eq(3)/Eq(4) consistency: OL-DEFER-03 (future campaign)
- Forward distortion model: not defined in this campaign

---

## T-11 — `fov_undistort_eq`

**File:** `FovModel.lean`
**Lean statement:**
```lean
theorem fov_undistort_eq
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε'_d ΔC ΔP : SensorPoint)
    (h  : denominatorNonzero k (sensorRadius (subSensorPoints ε'_d ΔC)))
    (h' : denominatorNonzero k (sensorRadius (subSensorPoints (subSensorPoints (addSensorPoints ε'_d ΔP) ΔC) ΔP))) :
    undistortFromDistorted k p (addSensorPoints ε'_d ΔP) ΔC ΔP h' =
    addSensorPoints (fovUndistortFromDistorted k p ε'_d ΔC h) ΔP
```
**Intended meaning:** When ε_d = ε'_d + ΔP (Eq 13, AMB-OL-002), the projection-form undistortion (Eq 4) equals the FOV-form undistortion (Eq 10) plus ΔP. This is the structural consistency theorem connecting the two characterisations.

**⚠ Scope limitation:** This theorem proves structural output consistency — that both forms compute the same SensorPoint given the Eq(13) translation hypothesis. It is NOT a full Eq(3)/Eq(4) equivalence proof. In particular:
- It does not prove that the forward projections agree.
- It does not prove roundtrip correctness.
- It does not establish injectivity or surjectivity of U.
- Full projection/FOV equivalence (including overscan) requires AMB-OL-008 resolution and OL-DEFER-03.

The two domain hypotheses `h` and `h'` are propositionally equal (by `distortion_center_translation_commutes`) but definitionally distinct — they are at different SensorPoint expressions. The proof uses `undistortPoint_congr` to bridge this gap.

**Proof strategy:** `simp only` unfolds both definitions; `congr 1; congr 1` reduces to showing the two `undistortPoint` calls agree; `undistortPoint_congr` applies `distortion_center_translation_commutes` to establish SensorPoint argument equality and closes by Lean 4 proof irrelevance.
**Classification:** substantive, structural, **partial**
**Deferred obligations:**
- Full projection/FOV equivalence under overscan: AMB-OL-008, AMB-OL-015
- Forward direction consistency: OL-DEFER-03

---

## T-12 — `angle_of_view_eq`

**File:** `AngleOfView.lean`
**Lean statement:**
```lean
theorem angle_of_view_eq (F r_u : ℝ) :
    Real.tan (angleOfView F r_u / 2) = r_u / F
```
**Intended meaning:** The tangent of half the angle of view equals r_u / F (§2 Eq 6). Inverts the `arctan` in `angleOfView`'s definition using `Real.tan_arctan` from Mathlib.

**Junk-value note (VAC-02):** The theorem is stated for all `F : ℝ` including F = 0. At F = 0, Lean's total division gives `r_u / 0 = 0`, `arctan 0 = 0`, `tan 0 = 0` — both sides are 0, so the theorem holds. This is a junk-value artifact of total division, not a physical claim. Physical use requires F > 0, enforced by `ValidLensSemantics` at call sites. The file documents this explicitly.

**Proof:** `simp [angleOfView, Real.tan_arctan]`
**Classification:** substantive (for F ≠ 0), algebraic, partial (junk-value at F = 0)
**Scope limitations:** Does not require F > 0 as a hypothesis. Physical correctness is a caller obligation via `ValidLensSemantics`.
**Deferred obligations:** A future authorized strengthening could add `hF : 0 < F` as a hypothesis (RW-02 in audit report), requiring explicit caller changes. Not authorized in this campaign.

---

## T-13 — `pixel_metric_roundtrip`

**File:** `ShaderCoords.lean`
**Lean statement:**
```lean
theorem pixel_metric_roundtrip
    (w h wshader : ℝ) (hw : 0 < w) (hh : 0 < h) (hs : 0 < wshader)
    (p : SensorPoint) :
    fromShaderCoords w h wshader (toShaderCoords w h wshader p) = p
```
**Intended meaning:** The shader-to-metric conversion is a left inverse of metric-to-shader: converting a sensor coordinate to shader space and back yields the original (§4.2 Eq 18 roundtrip, metric → shader → metric).
**Statement match:** Exact.
**Proof:** `ext <;> simp [...] <;> field_simp [hw.ne', hh.ne', hs.ne']` — `field_simp` clears denominators and closes both components.
**Classification:** substantive, algebraic, structural
**Scope limitations:** Requires w, h, wshader > 0. The inverse direction (T-14) requires a separate proof.
**Deferred obligations:** None.

---

## T-14 — `image_texture_coordinate_roundtrip`

**File:** `ShaderCoords.lean`
**Lean statement:**
```lean
theorem image_texture_coordinate_roundtrip
    (w h wshader : ℝ) (hw : 0 < w) (hh : 0 < h) (hs : 0 < wshader)
    (q : SensorPoint) :
    toShaderCoords w h wshader (fromShaderCoords w h wshader q) = q
```
**Intended meaning:** The metric-to-shader conversion is a left inverse of shader-to-metric: converting a shader coordinate to metric space and back yields the original (§4.2 Eq 18 roundtrip, shader → metric → shader).
**Statement match:** Exact.
**Proof:** `ext <;> simp [...] <;> field_simp [...] <;> ring` — `field_simp` leaves a residual arithmetic goal closed by `ring`.
**Classification:** substantive, algebraic, structural
**Scope limitations:** Same as T-13.
**Deferred obligations:** None.

---

## Private Lemma — `undistortPoint_congr`

**File:** `FovModel.lean`
**Lean statement:**
```lean
private lemma undistortPoint_congr
    (k : RadialCoefficients) (p : TangentialCoefficients)
    {ε₁ ε₂ : SensorPoint} (hε : ε₁ = ε₂)
    (h₁ : denominatorNonzero k (sensorRadius ε₁))
    (h₂ : denominatorNonzero k (sensorRadius ε₂)) :
    undistortPoint k p ε₁ h₁ = undistortPoint k p ε₂ h₂
```
**Intended meaning:** `undistortPoint` is equal when given propositionally-equal SensorPoint arguments, regardless of which proof of `denominatorNonzero` is supplied. Uses Lean 4 proof irrelevance: after substituting `ε₁ = ε₂`, both domain proofs are proofs of the same `Prop`, so `rfl` closes by kernel-level proof irrelevance.
**Proof:** `subst hε; rfl`
**Classification:** stepping-stone (supports `fov_undistort_eq` only)
**Note:** Private — not part of the public API. Exists solely to bridge the two domain hypotheses in `fov_undistort_eq`.

---

## Summary Table

| # | Name | File | Class | Scope |
|---|------|------|-------|-------|
| T-01 | `sensorRadius_nonneg` | CoordinateTypes | domain-safety, step | Full |
| T-02 | `semanticExtraction_sound` | SemanticBridge | substantive, partial | F>0 only |
| T-03 | `radial_denominator_nonzero_zero_coeffs` | RadialPolynomial | domain-safety, step | Zero-coeff case |
| T-04 | `radial_zero_coefficients_identity` | RadialPolynomial | identity, step | All-zero coefficients |
| T-05 | `tangential_zero_coefficients_identity` | DistortionModel | step, identity | x-component, zero-tang |
| T-06 | `brown_conrady_zero_identity` | DistortionModel | substantive, identity | All-zero case |
| T-07 | `deltaP_characterisation` | DeltaSemantics | algebraic, structural | Roundtrip only; α-equiv to T-08 |
| T-08 | `deltaC_characterisation` | DeltaSemantics | algebraic, structural | Roundtrip only; α-equiv to T-07 |
| T-09 | `distortion_center_translation_commutes` | DeltaSemantics | algebraic, step | Argument equality only |
| T-10 | `projection_matrix_undistort_eq` | ProjectionModel | algebraic, structural, **partial** | Offset cancellation only; NOT Eq(3)/Eq(4) equivalence |
| T-11 | `fov_undistort_eq` | FovModel | substantive, structural, **partial** | Output consistency only; NOT full equivalence |
| T-12 | `angle_of_view_eq` | AngleOfView | substantive, partial | Junk-value at F=0 |
| T-13 | `pixel_metric_roundtrip` | ShaderCoords | substantive, algebraic | w,h,wshader>0 |
| T-14 | `image_texture_coordinate_roundtrip` | ShaderCoords | substantive, algebraic | w,h,wshader>0 |
| — | `undistortPoint_congr` *(private)* | FovModel | step | Supports T-11 only |

---

## Deferred Obligations Summary

| Item | Deferred to | Impact |
|------|-------------|--------|
| Full Eq(3)/Eq(4) forward/inverse equivalence | OL-DEFER-03 | T-10, T-11 remain partial |
| Forward distortion model | Future campaign | Required for full roundtrip |
| Overscan containment equivalence | AMB-OL-008, AMB-OL-015 | T-11 does not cover overscan |
| `ValidLensSemantics` strengthening | Future authorized slice | T-02 remains thin |
| Float↔ℝ bridging theorem | Future campaign (high-risk) | AMB-OL-016 |
| Injectivity of U | AMB-OL-010 | No roundtrip theorem in campaign |
