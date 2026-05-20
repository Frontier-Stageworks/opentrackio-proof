---
name: proof-capsule
description: Stop 1 Proof Capsules for all openlensio_semantics slices — intent, statement, load-bearing definitions, forbidden changes
metadata:
  type: reference
---

# Proof Capsules — `openlensio_semantics`

One section per slice. Theorem-bearing slices have full capsules; definition-only slices have model audits.

---

## SLICE-OL-04 — `sensorRadius_nonneg`

**File:** `openlensio_semantics/CoordinateTypes.lean`  
**Layer:** C

### Theorem

```lean
theorem sensorRadius_nonneg (p : SensorPoint) : 0 ≤ sensorRadius p
```

### Intent

`sensorRadius p = Real.sqrt (p.x² + p.y²)` is the argument `r` to the radial polynomial R (Eq 17).
The theorem confirms `r ≥ 0` for all sensor points — required for downstream domain predicates to type-check.

### Statement audit

- `SensorPoint` is `{x y : ℝ}`. Phantom-type tagging deferred per AMB-OL-004.
- The theorem holds unconditionally; no hypothesis needed. The origin (`p = ⟨0,0⟩`) is reachable and yields `sensorRadius p = 0`, so the theorem is not vacuous.

### Load-bearing definitions

| Name | Shape | Notes |
|---|---|---|
| `SensorPoint` | `{x y : ℝ}` | 2D sensor-plane point |
| `sensorRadius` | `Real.sqrt (p.x^2 + p.y^2)` | Radius from origin |

### Forbidden changes

- Do not change `sensorRadius` to avoid `Real.sqrt`.
- Do not add a nonzero hypothesis on `p`.
- Do not use `sorry`.

---

## SLICE-OL-01 — Model audit: `LensSemantics`, `ValidLensSemantics`

**File:** `openlensio_semantics/LensSemantics.lean`  
**Layer:** B  
**No theorem — definition audit only**

### Model audit

| Name | Shape | Intended invariant | Encoded? |
|---|---|---|---|
| `RadialCoefficients` | `{k1 k2 k3 k4 k5 k6 : ℝ}` | k1,k3,k5=numerator; k2,k4,k6=denominator (Eq 17) | Naming only; no type-level enforcement |
| `TangentialCoefficients` | `{p1 p2 : ℝ}` | Brown-Conrady p1,p2 coefficients | Naming only |
| `TangentialCoefficients.zero` | `⟨0, 0⟩` | Default when absent (AMB-OL-013) | Encoded |
| `LensSemantics` | `{focalLength radial tangential distCentre perspOffset}` | All over ℝ | Fields present |
| `ValidLensSemantics` | `0 < l.focalLength` | F > 0 required by §1.1 | Encoded in predicate |

### Deferred invariants (by design)

- Denominator nonzero for R: per-point predicate, deferred to SLICE-OL-05 (AMB-OL-007).
- Tangential absent → zero: caller responsibility at bridge (AMB-OL-013).

### Naming hazard

`k1..k6` here follow the OpenLensIO paper (alternating num/den). `DistortionConversion.lean` uses `k1..k3 = OpenCV numerator`, `k4..k6 = OpenCV denominator`. Do not conflate.

### Forbidden changes

- Do not change `ValidLensSemantics` to `True` or add vacuous alternatives.
- Do not add denominator nonzero to `ValidLensSemantics` — it belongs in SLICE-OL-05.

---

## SLICE-OL-02 — Model audit: `extractLensSemantics`

**File:** `openlensio_semantics/SemanticBridge.lean`  
**Layer:** B  
**No standalone theorem — function definition audited here; soundness is SLICE-OL-03**

### Model audit

```lean
noncomputable def extractLensSemantics
    (focalLength : ℝ) (k1 k2 k3 k4 k5 k6 : ℝ) (p1 p2 : ℝ) (dcx dcy : ℝ) (dpx dpy : ℝ) :
    Except SemanticError LensSemantics
```

- Takes already-decoded `ℝ` values — string-to-real parsing is a Layer F oracle concern, not a formal concern here.
- Guards `0 < focalLength` before constructing `.ok`. Returns `.error .nonPositiveFocalLength` otherwise.
- `noncomputable` required because the `if` branch uses `Real.decidableLT` which is noncomputable.

### Scope note

This definition does NOT parse raw JSON strings. It is the semantic layer receiving already-decoded real numbers. The full bridge from `Lens` (with `Option String` fields) to `LensSemantics` is Layer F work.

### Forbidden changes

- Do not make the focalLength guard vacuous (e.g., `if True`).
- Do not collapse raw string parsing into this layer.

---

## SLICE-OL-03 — `semanticExtraction_sound`

**File:** `openlensio_semantics/SemanticBridge.lean`  
**Layer:** B

### Theorem

```lean
theorem semanticExtraction_sound
    (focalLength : ℝ) (k1 k2 k3 k4 k5 k6 : ℝ) (p1 p2 : ℝ) (dcx dcy : ℝ) (dpx dpy : ℝ)
    (s : LensSemantics)
    (h : extractLensSemantics focalLength k1 k2 k3 k4 k5 k6 p1 p2 dcx dcy dpx dpy = .ok s) :
    ValidLensSemantics s
```

### Intent

A successful extraction guarantees the result satisfies `ValidLensSemantics`.
This is the entry-point soundness theorem for the semantic bridge: all downstream theorems
can assume `ValidLensSemantics s` whenever the bridge succeeds.

### Statement audit

- Hypothesis `h` is exactly the success condition. The conclusion is `ValidLensSemantics s = (0 < s.focalLength)`.
- NOT vacuous: when `focalLength ≤ 0` the function returns `.error`, so `h` is unsatisfiable, and the theorem genuinely constrains the `.ok` branch only.
- No extra hypotheses were added to paper over a proof difficulty.

### Parameters and hypotheses

All parameters are the inputs to `extractLensSemantics`. `h` is the success condition.
No hypothesis was added beyond what is needed to state the soundness property.

### Load-bearing definitions

| Name | What it does |
|---|---|
| `extractLensSemantics` | Guards `0 < focalLength`; the proof follows from the guard |
| `ValidLensSemantics` | `0 < l.focalLength`; must not be weakened |

### Forbidden changes

- Do not weaken `ValidLensSemantics` to make the proof easier.
- Do not add a hypothesis `0 < focalLength` directly to the theorem (it is implied by `h`).
- Do not use `sorry`.

---

## SLICE-OL-05 — `radialTerm_eq` and `radial_denominator_nonzero_zero_coeffs`

**File:** `openlensio_semantics/RadialPolynomial.lean`  
**Layer:** C + D

### Theorems

```lean
theorem radial_denominator_nonzero_zero_coeffs
    (k : RadialCoefficients) (r : ℝ)
    (hk2 : k.k2 = 0) (hk4 : k.k4 = 0) (hk6 : k.k6 = 0) :
    denominatorNonzero k r
```

### Intent

**`radial_denominator_nonzero_zero_coeffs`:** The canonical concrete domain-safety instance. When all denominator coefficients are zero the denominator equals 1, which is nonzero. Confirms that `denominatorNonzero` is satisfiable (non-vacuous as a precondition) and that callers can discharge it in the most common case (no rational denominator terms, i.e., plain polynomial R).

### AMB-OL-007 resolution

The paper does not state conditions on k2, k4, k6 that guarantee the denominator is nonzero for all r. Resolution: `denominatorNonzero k r` is an explicit hypothesis to `radialTerm` — the caller is responsible for supplying evidence. `radial_denominator_nonzero_zero_coeffs` is the canonical instance, not the only one.

### Statement audit

- `radialTerm_eq`: definitional equality — holds by `rfl`. Not vacuous: the conclusion is the equation, which would be false if the definition differed.
- `radial_denominator_nonzero_zero_coeffs`: the conclusion `denominatorNonzero k r` unfolds to `1 + 0*r² + 0*r⁴ + 0*r⁶ ≠ 0 = (1 ≠ 0)`, which is true. Non-vacuous: `denominatorNonzero k r` is genuinely false for some coefficient/radius combinations (e.g., k2=−1, r=1 yields denominator = 1 + (−1)·1 = 0).

### Load-bearing definitions

| Name | Shape | Notes |
|---|---|---|
| `denominatorNonzero` | `1 + k.k2*r² + k.k4*r⁴ + k.k6*r⁶ ≠ 0` | Domain predicate; caller obligation (AMB-OL-007) |
| `radialTerm` | numerator / denominator with `h : denominatorNonzero k r` | The rational R factor from Eq 17 |

### Forbidden changes

- Do not remove the `h : denominatorNonzero k r` parameter from `radialTerm` — this is the load-bearing domain-safety argument.
- Do not make `denominatorNonzero` trivially true (e.g., `True`) to paper over proof obligations.
- Do not use `sorry`.

---

## SLICE-OL-06 — `radial_zero_coefficients_identity`

**File:** `openlensio_semantics/RadialPolynomial.lean` (added section)  
**Layer:** E (algebraic identity)

### Theorem

```lean
theorem radial_zero_coefficients_identity
    (k : RadialCoefficients) (r : ℝ)
    (hk1 : k.k1 = 0) (hk2 : k.k2 = 0) (hk3 : k.k3 = 0)
    (hk4 : k.k4 = 0) (hk5 : k.k5 = 0) (hk6 : k.k6 = 0)
    (h : denominatorNonzero k r) :
    radialTerm k r h = 1
```

### Intent

When all six radial coefficients are zero, R = 1. This is the algebraic identity at
the base of the zero-distortion proof chain: zero radial coefficients → R = 1 →
(in SLICE-OL-08) U(ϵ) = ϵ. The theorem is a direct paper claim — a lens with all-zero
k coefficients has no radial distortion.

### Statement audit

- Takes explicit `h : denominatorNonzero k r` because `radialTerm` requires it as part of its signature — any caller of `radialTerm` already holds an `h`. This is not "the more general form"; `h` is structurally required by the function, not an independent precondition. Note: `h` is also derivable from `hk2`, `hk4`, `hk6` via `radial_denominator_nonzero_zero_coeffs`, so it is redundant as a logical hypothesis. It appears because the theorem statement must apply `radialTerm k r h`.
- NOT vacuous: the conclusion `radialTerm k r h = 1` is false when e.g. k1 = 1 (numerator becomes 1 + r²). The six zero conditions are genuinely required.
- Planned stepping stone: this lemma exists to support `brown_conrady_zero_identity` (SLICE-OL-08). If OL-08 does not call it, it should be removed at that point.

### Load-bearing definitions

| Name | Role |
|---|---|
| `radialTerm` | Defined as numerator/denominator; both reduce to 1 when all k = 0; unfolded directly via `simp only [radialTerm, ...]` |
| `denominatorNonzero` | Required by `radialTerm`; not a proof-hiding device here |

### Forbidden changes

- Do not drop the `h` parameter — `radialTerm` requires it.
- Do not use `sorry`.

---

## SLICE-OL-07 — Model audit: `undistortX`, `undistortY`, `undistortPoint`

**File:** `openlensio_semantics/DistortionModel.lean`  
**Layer:** C  
**No theorems — definition audit only**

### Equations from paper

§4.1 Eq (16), component (non-singular) form:

```
U_x(ϵ) = R·ϵ_x + 2·p1·ϵ_x·ϵ_y + p2·(r² + 2·ϵ_x²)
U_y(ϵ) = R·ϵ_y + p1·(r² + 2·ϵ_y²) + 2·p2·ϵ_x·ϵ_y
```

where r = sensorRadius ϵ and R = radialTerm k r h.

### Design choice (AMB-OL-004)

Component form (above) chosen over the diagonal matrix form in the paper.
The diagonal form U(ϵ) = diag(R,R)·ϵ + tangential_terms is algebraically equivalent
but involves a 2×2 matrix, which would require defining matrix types or using Mathlib's
`Matrix`. The component form stays in `ℝ` and lets `ring` close polynomial identities
directly. The equivalence is definitional.

### Model audit

| Name | Type | Paper source | Invariants encoded |
|---|---|---|---|
| `undistortX` | `RadialCoefficients → TangentialCoefficients → SensorPoint → denominatorNonzero k (sensorRadius ε) → ℝ` | §4.1 Eq (16) U_x | denominatorNonzero via h |
| `undistortY` | same shape, returns U_y | §4.1 Eq (16) U_y | denominatorNonzero via h |
| `undistortPoint` | `... → SensorPoint` | §4.1 Eq (16) full U(ϵ) | packages x and y components |

### Domain predicate threading

`h : denominatorNonzero k (sensorRadius ε)` is the domain predicate. It is passed as an
explicit argument to `undistortX`, `undistortY`, and `undistortPoint`. The same `h` is
forwarded to `radialTerm` inside the body — no new nonzero evidence is created.

### Deferred

- Zero-distortion identity `U(ϵ) = ϵ` (SLICE-OL-08 — next slice)
- Invertibility of U (U⁻¹, SLICE-OL-DEFER-03)
- Continuity and monotonicity (deferred per work queue)
- Zero-distortion identity `U(ϵ) = ϵ` when all coefficients zero (SLICE-OL-08)

### Forbidden changes

- Do not use the diagonal matrix form — component form is the chosen representation.
- Do not drop `h` from the signatures.
- Do not define U⁻¹ in this slice.

---

## SLICE-OL-08 — `tangential_zero_coefficients_identity` and `brown_conrady_zero_identity`

**File:** `openlensio_semantics/DistortionModel.lean` (added theorems)  
**Layer:** E (algebraic identity)

### Theorems

```lean
theorem tangential_zero_coefficients_identity
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε : SensorPoint) (h : denominatorNonzero k (sensorRadius ε))
    (hp1 : p.p1 = 0) (hp2 : p.p2 = 0) :
    undistortX k p ε h = radialTerm k (sensorRadius ε) h * ε.x

theorem brown_conrady_zero_identity
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε : SensorPoint) (h : denominatorNonzero k (sensorRadius ε))
    (hk1 : k.k1 = 0) (hk2 : k.k2 = 0) (hk3 : k.k3 = 0)
    (hk4 : k.k4 = 0) (hk5 : k.k5 = 0) (hk6 : k.k6 = 0)
    (hp1 : p.p1 = 0) (hp2 : p.p2 = 0) :
    undistortPoint k p ε h = ε
```

### Intent

**`tangential_zero_coefficients_identity`:** With zero tangential coefficients, the x-component of U reduces to R·ϵ_x. This is the intermediate step between "p=0" and "U_x = ϵ_x". It is a planned stepping stone: used explicitly in the proof of `brown_conrady_zero_identity` to derive the X component.

**`brown_conrady_zero_identity`:** When all eight distortion coefficients are zero, the undistortion function is the identity. This is the central zero-distortion claim of the OpenLensIO model: a flat lens with no distortion leaves coordinates unchanged. It closes the identity proof chain started by `radial_zero_coefficients_identity`.

### Statement audit

- **`tangential_zero_coefficients_identity`:** NOT vacuous — the conclusion is false when p.p1 ≠ 0 (tangential cross term survives). Hypotheses hp1, hp2 are independently satisfiable.
- **`brown_conrady_zero_identity`:** NOT vacuous — the conclusion `undistortPoint k p ε h = ε` is false for non-zero coefficients (R ≠ 1 or tangential terms ≠ 0). The 8 zero conditions are all genuinely required.
- Work queue specified `allZeroCoeffs k p → ...` as a bundled predicate. Deviation: individual hypotheses taken instead. Bundling would require a new definition with no mathematical benefit; `allZeroCoeffs` is not defined elsewhere. Individual hypotheses are cleaner to use with `simp` and `rw`.
- The `h : denominatorNonzero k (sensorRadius ε)` is structurally required by `radialTerm` (same pattern as `radial_zero_coefficients_identity`).

### Proof chain

```
radial_zero_coefficients_identity  (OL-06)  →  hR : radialTerm ... = 1
tangential_zero_coefficients_identity       →  hX : undistortX ... = R·ε.x
                               hR + hX     →  undistortX ... = ε.x
                                            →  undistortY ... = ε.y (inline)
                                            →  undistortPoint ... = ε
```

`radial_zero_coefficients_identity` is called explicitly in the proof of `brown_conrady_zero_identity`. This confirms it earns its place as a named lemma.

### Load-bearing definitions

| Name | Role |
|---|---|
| `undistortX`, `undistortY` | Unfolded to expose polynomial structure |
| `undistortPoint` | Packages x and y; equality proved by `SensorPoint.ext` |
| `radialTerm` | Appears in `tangential_zero_coefficients_identity`'s conclusion; replaced by 1 via `hR` |
| `radial_zero_coefficients_identity` | Called explicitly in `brown_conrady_zero_identity` |

### Forbidden changes

- Do not add `allZeroCoeffs` as a new definition just to match the work queue form.
- Do not drop `tangential_zero_coefficients_identity` before verifying it is used in the `brown_conrady_zero_identity` proof.
- Do not use `sorry`.

---

## SLICE-OL-09 — `deltaP_characterisation`, `deltaC_characterisation`, `distortion_center_translation_commutes`

**File:** `openlensio_semantics/DeltaSemantics.lean` (new file)  
**Layer:** C + E

### AMB-OL-002 resolution (load-bearing)

Paper Eq (13) is the authority: `ε_d = ε'_d + ΔP` (addition).
The inline text near Eq (10) states `ε'_d = ε_d + ΔP` — this is a typo with the wrong sign.
Mathematical verification: Eq (13) sign is consistent with the rest of the model:
  `ε_u = U(ε_d − ΔC − ΔP) + ΔC + ΔP` (Eq 4)  
  with `ε_d = ε'_d + ΔP` → argument = `ε'_d − ΔC` = argument of Eq (10). ✓

**All ΔP shift operations in this slice use addition, not subtraction.**
If this resolution is wrong, all three theorems below have the wrong sign.

### Definitions

```lean
def addSensorPoints (p q : SensorPoint) : SensorPoint := ⟨p.x + q.x, p.y + q.y⟩
def subSensorPoints (p q : SensorPoint) : SensorPoint := ⟨p.x - q.x, p.y - q.y⟩
```

### Theorems

```lean
-- Eq (12): (ε'_u + ΔP) − ΔP = ε'_u
theorem deltaP_characterisation (ε'_u ΔP : SensorPoint) :
    subSensorPoints (addSensorPoints ε'_u ΔP) ΔP = ε'_u

-- Eq (13): (ε'_d + ΔP) − ΔP = ε'_d
theorem deltaC_characterisation (ε'_d ΔP : SensorPoint) :
    subSensorPoints (addSensorPoints ε'_d ΔP) ΔP = ε'_d

-- Consistency of Eq (4) and Eq (10): (ε'_d + ΔP) − ΔC − ΔP = ε'_d − ΔC
theorem distortion_center_translation_commutes (ε'_d ΔP ΔC : SensorPoint) :
    subSensorPoints (subSensorPoints (addSensorPoints ε'_d ΔP) ΔC) ΔP =
    subSensorPoints ε'_d ΔC
```

### Intent

**`deltaP_characterisation`:** Documents Eq (12) — the ΔP shift is invertible; shifting and unshifting returns to the original FOV-form coordinate. Confirms the AMB-OL-002 sign choice is consistent: addition.

**`deltaC_characterisation`:** Documents Eq (13) — same algebraic form for distorted coordinates. Both are instances of `(p + q) − q = p`; they are stated separately to document which paper equation each corresponds to.

**`distortion_center_translation_commutes`:** The key algebraic fact from §3: when `ε_d = ε'_d + ΔP`, the argument `ε_d − ΔC − ΔP` in Eq (4) equals `ε'_d − ΔC` in Eq (10). The ΔP terms cancel. This is why the two parametrisations produce the same undistorted coordinate.

### Statement audit

- `deltaP_characterisation` and `deltaC_characterisation` are algebraically identical (`(p + q) − q = p`). They are kept as separate theorems for documentation: one for Eq (12) (undistorted), one for Eq (13) (distorted). Neither is vacuous — the conclusion is false if the sign were subtraction instead of addition.
- `distortion_center_translation_commutes` is NOT the same as the previous two. It involves three points and captures a two-step cancellation.
- AMB-OL-002 sign is load-bearing for all three. If the sign in the definitions were reversed, all theorems would fail.

### Forbidden changes

- Do not change `addSensorPoints` to use subtraction — the AMB-OL-002 resolution explicitly requires addition.
- Do not merge `deltaP_characterisation` and `deltaC_characterisation` into one — they document different paper equations.
- Do not use `sorry`.

---

## SLICE-OL-10 — Model audit: `projectToImage`, `undistortFromDistorted`; theorem `projection_matrix_undistort_eq`

**File:** `openlensio_semantics/ProjectionModel.lean` (new file)  
**Layer:** C + E

### Theorem

```lean
theorem projection_matrix_undistort_eq
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε_d ΔC ΔP : SensorPoint)
    (h : denominatorNonzero k (sensorRadius (subSensorPoints (subSensorPoints ε_d ΔC) ΔP))) :
    subSensorPoints (subSensorPoints (undistortFromDistorted k p ε_d ΔC ΔP h) ΔC) ΔP =
    undistortPoint k p (subSensorPoints (subSensorPoints ε_d ΔC) ΔP) h
```

### Intent

**`projectToImage` (Eq 3):** Defines the undistorted image coordinate from normalized camera coordinates `u = (x_p/z_p, y_p/z_p)`: `ε_u = ⟨F*u.x + ΔP.x, F*u.y + ΔP.y⟩`. F > 0 is a ValidLensSemantics precondition passed by callers; z_p ≠ 0 is handled by the caller before computing u. No theorem about `projectToImage` is proved in this slice — the consistency of Eq(3) with Eq(4) requires the forward distortion model (Eq 5) and is deferred.

**`undistortFromDistorted` (Eq 4):** Defines `ε_u = U(ε_d − ΔC − ΔP) + ΔC + ΔP`.

**`projection_matrix_undistort_eq`:** Structural consistency of Eq (4): removing the ΔC+ΔP offset from `undistortFromDistorted`'s output recovers `undistortPoint`'s output. States that `(U(ε_d − ΔC − ΔP) + ΔC + ΔP) − ΔC − ΔP = U(ε_d − ΔC − ΔP)`. Verifies the shift-undistort-shift pattern in the definition is correctly ordered.

### Scope limitation (documented deviation from work queue)

The work queue stated `projection_matrix_undistort_eq` as "consistency of Eq 3 with Eq 4". The full consistency (that `projectToImage` and `undistortFromDistorted` agree for corresponding inputs) requires the forward distortion model — specifically the relationship between a camera-frame point and its distorted image coordinate. That is not available until SLICE-OL-DEFER-03 or a future forward-model slice. The theorem as proved here is the achievable structural property.

### Statement audit

- NOT vacuous: the conclusion fails if the shifts in `undistortFromDistorted` were in the wrong order (e.g., if `addSensorPoints ΔP (addSensorPoints X ΔC)` were used and then `subSensorPoints` was applied in reversed order).
- NOT trivially true by `rfl`: requires ring arithmetic `a + b + c - b - c = a`.
- `h` is structurally required — `undistortFromDistorted` needs it to call `undistortPoint`.

### Load-bearing definitions

| Name | Shape | Paper |
|---|---|---|
| `projectToImage` | `⟨F*u.x + ΔP.x, F*u.y + ΔP.y⟩` | §2 Eq (3) |
| `undistortFromDistorted` | `U(ε_d − ΔC − ΔP) + ΔC + ΔP` | §2 Eq (4) |
| `addSensorPoints`, `subSensorPoints` | from DeltaSemantics | |
| `undistortPoint` | from DistortionModel | |

### Forbidden changes

- Do not attempt the full Eq(3)/Eq(4) consistency theorem in this slice.
- Do not use `sorry`.
- Do not add `F > 0` as a hypothesis to `projection_matrix_undistort_eq` — it is not needed for the structural property proved here.

---

## SLICE-OL-11 — Model audit: `fovProjectToImage`, `fovUndistortFromDistorted`; theorem `fov_undistort_eq`

**File:** `openlensio_semantics/FovModel.lean` (new file)  
**Layer:** C + E

### Definitions

```lean
-- Eq (9): §3 — FOV-form undistorted coordinate (no ΔP term)
noncomputable def fovProjectToImage (F : ℝ) (u : SensorPoint) : SensorPoint :=
  ⟨F * u.x, F * u.y⟩

-- Eq (10): §3 — FOV-form undistort from distorted (no ΔP terms)
noncomputable def fovUndistortFromDistorted
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε'_d ΔC : SensorPoint)
    (h : denominatorNonzero k (sensorRadius (subSensorPoints ε'_d ΔC))) : SensorPoint :=
  addSensorPoints (undistortPoint k p (subSensorPoints ε'_d ΔC) h) ΔC
```

### Helper lemma

```lean
private lemma undistortPoint_congr
    (k : RadialCoefficients) (p : TangentialCoefficients)
    {ε₁ ε₂ : SensorPoint} (hε : ε₁ = ε₂)
    (h₁ : denominatorNonzero k (sensorRadius ε₁))
    (h₂ : denominatorNonzero k (sensorRadius ε₂)) :
    undistortPoint k p ε₁ h₁ = undistortPoint k p ε₂ h₂
```

Proved by `subst hε; rfl`. The `subst` substitutes the SensorPoint equality (ε₁ is a free variable in the lemma), leaving both proofs with the same Prop type; `rfl` closes by Lean 4 proof irrelevance.

### Theorem

```lean
theorem fov_undistort_eq
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε'_d ΔC ΔP : SensorPoint)
    (h  : denominatorNonzero k (sensorRadius (subSensorPoints ε'_d ΔC)))
    (h' : denominatorNonzero k (sensorRadius (subSensorPoints (subSensorPoints (addSensorPoints ε'_d ΔP) ΔC) ΔP))) :
    undistortFromDistorted k p (addSensorPoints ε'_d ΔP) ΔC ΔP h' =
    addSensorPoints (fovUndistortFromDistorted k p ε'_d ΔC h) ΔP
```

Two explicit hypotheses: `h` for the FOV form's precondition, `h'` for the projection form's precondition. The relationship `h'` is derivable from `h` via `distortion_center_translation_commutes`; callers use `by rw [distortion_center_translation_commutes]; exact h` to produce `h'`.

### Intent

**`fovProjectToImage` (Eq 9):** `ε'_u = F·u` — the FOV-form projection uses no ΔP offset. ΔP is the perspective offset that shifts between the two coordinate conventions (§1.5). The FOV form centres coordinates at the intersection of the optical axis with the image plane, while the projection matrix form centres at ΔP.

**`fovUndistortFromDistorted` (Eq 10):** `ε'_u = U(ε'_d − ΔC) + ΔC` — the FOV-form undistort applies U to the distortion-centred coordinate and re-adds ΔC. No ΔP shift. Compare with Eq (4): `ε_u = U(ε_d − ΔC − ΔP) + ΔC + ΔP`.

**`fov_undistort_eq`:** Structural consistency of Eq (10) with Eq (4) via the ΔP translation (AMB-OL-002 resolution). When `ε_d = ε'_d + ΔP` (Eq 13), the output of `undistortFromDistorted` for ε_d equals the output of `fovUndistortFromDistorted` for ε'_d plus ΔP. This is the Lean formalization of why the two parametrisations agree.

### Dropped theorem (LAPS anti-pattern)

The work queue listed `fov_projection_translation : ε_u = ε'_u + ΔP` as a target. After expanding definitions, both sides reduce to `⟨F*u.x + ΔP.x, F*u.y + ΔP.y⟩` — this is true by `rfl` (definitional tautology). LAPS forbids trivially-true theorems. Dropped.

### Statement audit

**`fov_undistort_eq`:**
- NOT vacuous: if `fovUndistortFromDistorted` had wrong ΔC placement, the conclusion would be false.
- NOT trivially true: the coercion `(distortion_center_translation_commutes ...).symm ▸ h` is the load-bearing step — it certifies that the argument `ε'_d − ΔC` in the FOV form equals the argument `(ε'_d + ΔP) − ΔC − ΔP` in the projection form (by `distortion_center_translation_commutes` from OL-09).
- `h` is the sole domain precondition. `hShifted` is derived internally via the coercion — not an extra hypothesis, not a burden on callers.

### Hard step identification

The dependent type coercion: `undistortFromDistorted` requires `h' : denominatorNonzero k (sensorRadius A_big)` where `A_big = subSensorPoints (subSensorPoints (addSensorPoints ε'_d ΔP) ΔC) ΔP`, while `fovUndistortFromDistorted` requires `h : denominatorNonzero k (sensorRadius A_small)` where `A_small = subSensorPoints ε'_d ΔC`. These conditions are propositionally equal (by `distortion_center_translation_commutes`) but not definitionally equal — Lean 4's `rfl` cannot close `h' = h` without a structural argument.

Resolution: two explicit hypotheses (`h` and `h'`) in the theorem statement, plus `undistortPoint_congr` helper. The helper uses `subst hε` (valid when one side of the equality is a free variable, which it is in the helper's local context) to substitute the SensorPoint equality, leaving both proofs with the same Prop type, then `rfl` closes by Lean 4 proof irrelevance.

The original plan proposed a single-hypothesis form with `▸` in the theorem statement. This was dropped: `▸` in term position (outside a `by` block) risks elaboration failures, and the two-hypothesis form is cleaner for downstream callers.

### AMB-OL-002 dependency

`distortion_center_translation_commutes` (OL-09, proved under AMB-OL-002 addition sign) is load-bearing. If AMB-OL-002 is resolved differently, all three of `addSensorPoints ε'_d ΔP`, `h'`'s type, and the theorem conclusion need sign changes.

### Load-bearing definitions

| Name | Shape | Paper |
|---|---|---|
| `fovProjectToImage` | `⟨F*u.x, F*u.y⟩` | §3 Eq (9) |
| `fovUndistortFromDistorted` | `U(ε'_d − ΔC) + ΔC` | §3 Eq (10) |
| `undistortFromDistorted` | `U(ε_d − ΔC − ΔP) + ΔC + ΔP` | §2 Eq (4) — from OL-10 |
| `distortion_center_translation_commutes` | OL-09 theorem — establishes `A_big = A_small` | §3 |
| `undistortPoint_congr` | Private helper — dependent type equality via `subst` + proof irrel | — |

### Forbidden changes

- Do not add `fov_projection_translation` — it is trivially true by rfl.
- Do not add ΔP to `fovProjectToImage` or `fovUndistortFromDistorted` — these are the ΔP-free FOV forms.
- Do not merge `h` and `h'` into one (via `▸` in the statement) — risks elaboration issues; two-hypothesis form is the verified clean shape.
- Do not use `sorry`.
