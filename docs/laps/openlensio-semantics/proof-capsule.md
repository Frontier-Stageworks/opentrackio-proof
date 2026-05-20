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
theorem radialTerm_eq (k : RadialCoefficients) (r : ℝ) (h : denominatorNonzero k r) :
    radialTerm k r h =
    (1 + k.k1 * r ^ 2 + k.k3 * r ^ 4 + k.k5 * r ^ 6) /
    (1 + k.k2 * r ^ 2 + k.k4 * r ^ 4 + k.k6 * r ^ 6)

theorem radial_denominator_nonzero_zero_coeffs
    (k : RadialCoefficients) (r : ℝ)
    (hk2 : k.k2 = 0) (hk4 : k.k4 = 0) (hk6 : k.k6 = 0) :
    denominatorNonzero k r
```

### Intent

**`radialTerm_eq`:** States the defining equation of the radial factor R (§4.1 Eq 17) as a theorem for downstream use (rewriting in proofs of distortion lemmas).

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

- Takes explicit `h : denominatorNonzero k r` so the statement is valid for any denominator-nonzero instance, not just the zero-coefficient one. This is the more general (stronger) form; callers can supply `radial_denominator_nonzero_zero_coeffs` when needed.
- NOT vacuous: the conclusion `radialTerm k r h = 1` is false when e.g. k1 = 1 (numerator becomes 1 + r²).
- No extra hypotheses beyond what's needed: the six zero conditions are exactly sufficient.

### Load-bearing definitions

| Name | Role |
|---|---|
| `radialTerm` | Defined as numerator/denominator; both reduce to 1 when all k = 0 |
| `radialTerm_eq` | Used as a rewrite lemma to expose the fraction |
| `denominatorNonzero` | Required by `radialTerm`; not a proof-hiding device here |

### Forbidden changes

- Do not drop the `h` parameter and use a default proof — the explicit hypothesis is load-bearing design.
- Do not change `radialTerm_eq` to accommodate the proof.
- Do not use `sorry`.
