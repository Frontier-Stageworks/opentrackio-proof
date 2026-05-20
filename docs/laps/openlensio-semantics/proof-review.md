---
name: proof-review
description: Stop 4 Proof Reviews for all openlensio_semantics slices — kernel status, semantic match, anti-pattern scan
metadata:
  type: reference
---

# Proof Reviews — `openlensio_semantics`

One section per theorem-bearing slice.

---

## SLICE-OL-04 — `sensorRadius_nonneg`

**Build:** `lake build CoordinateTypes` — ✅ clean  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`. Standard Mathlib axioms only.

### Theorem statement unchanged

Authorized: `theorem sensorRadius_nonneg (p : SensorPoint) : 0 ≤ sensorRadius p`  
Final: identical.

### Semantic match

The intent is that `sensorRadius p ≥ 0` always, so it can safely be passed to the radial polynomial without a sign check. The formal statement is exactly this. Non-vacuous: the origin yields `sensorRadius ⟨0,0⟩ = 0`, which satisfies `0 ≤ 0` but is not trivially positive.

### Proof structure

`Real.sqrt_nonneg _` — single proof term. The Mathlib lemma `Real.sqrt_nonneg : ∀ x, 0 ≤ Real.sqrt x` applies directly.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Hidden sorry | ✅ None |
| Extra hypothesis to make proof easier | ✅ None — no hypothesis needed |
| Vacuous statement | ✅ Non-vacuous (origin is a valid input) |
| Wrong definition of sensorRadius | ✅ Matches §1.1 `r = √(ϵ_x² + ϵ_y²)` |

---

## SLICE-OL-03 — `semanticExtraction_sound`

**Build:** `lake build SemanticBridge` — ✅ clean (3288 jobs)  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`. Standard Mathlib axioms only.

### Theorem statement unchanged

Authorized and final statements are identical (see proof-capsule.md SLICE-OL-03 section).

### Semantic match

**Intended claim:** A successful extraction guarantees `ValidLensSemantics`.  
**Formal conclusion:** `ValidLensSemantics s` — exactly the intended claim.  
**Non-vacuity:** The error branch (focalLength ≤ 0) is reachable; the theorem does not hold for all inputs, only those for which extraction succeeds. Genuine constraint.

### Hypothesis justification

All parameters are the inputs to `extractLensSemantics`. No hypothesis was added beyond `h : ... = .ok s` (the success condition). `h` is the minimal hypothesis for soundness.

### Proof structure and hard step

- `unfold extractLensSemantics at h` — exposes the if-then-else
- `split_ifs at h with hf` — splits; negative branch auto-closed by contradiction
- `simp only [Except.ok.injEq] at h` + `subst h` — injects and substitutes
- `exact hf` — closes with the branch hypothesis

**Hard step:** none. The theorem is a direct consequence of the if-guard.

### Load-bearing definition alignment

- `extractLensSemantics`: guards `0 < focalLength`; proof depends on this guard — definition unchanged.
- `ValidLensSemantics`: `0 < l.focalLength` — definition unchanged; not weakened.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Hidden sorry | ✅ None |
| `ValidLensSemantics` weakened | ✅ Unchanged |
| Extra hypothesis to trivialize | ✅ None added |
| Vacuous theorem | ✅ Non-vacuous |
| Broad `simp` hiding hard step | ✅ `simp only [Except.ok.injEq]` — explicit lemma |
| Wrong layer (raw strings in bridge) | ✅ Bridge receives ℝ values, not strings |

---

## SLICE-OL-05 — `radial_denominator_nonzero_zero_coeffs`

**Build:** `lake build RadialPolynomial` — ✅ clean  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`. Standard Mathlib axioms only.

### Theorem statement unchanged

Matches proof-capsule.md SLICE-OL-05 section. `radialTerm_eq` was removed — it was a trivially-true definitional tautology added speculatively; `simp only [radialTerm, ...]` serves the same purpose directly.

### Semantic match

**`radial_denominator_nonzero_zero_coeffs`:** Intent is to confirm `denominatorNonzero` is satisfiable (non-vacuous precondition) and to provide the canonical instance for zero denominator coefficients. The conclusion unfolds to `1 ≠ 0` after substitution — a genuine fact, not tautological.

Non-vacuity of `denominatorNonzero`: the predicate fails for `k.k2 = -1, r = 1` (denominator = 0). It is not always true, so callers genuinely need to discharge it.

### Load-bearing definition alignment

- `denominatorNonzero`: `1 + k.k2 * r^2 + k.k4 * r^4 + k.k6 * r^6 ≠ 0` — exactly the denominator of R from Eq 17. Not weakened or trivialized.
- `radialTerm`: takes `(_ : denominatorNonzero k r)` as a proof-irrelevant parameter — the load-bearing domain-safety argument is present and required.

### Proof structure

- `radialTerm_eq`: `rfl` — definitional equality.
- `radial_denominator_nonzero_zero_coeffs`: `simp [denominatorNonzero, hk2, hk4, hk6]` — substitutes zero coefficients, simplifies arithmetic, closes `1 ≠ 0` via `one_ne_zero`.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Hidden sorry | ✅ None |
| `denominatorNonzero` trivialized | ✅ Genuinely constraining predicate |
| Domain-safety hypothesis removed | ✅ Present in `radialTerm` signature |
| Vacuous theorem | ✅ Non-vacuous (predicate fails for k2=−1, r=1) |
| Wrong Eq 17 numerator/denominator assignment | ✅ k1,k3,k5=numerator; k2,k4,k6=denominator (paper convention) |

---

## SLICE-OL-06 — `radial_zero_coefficients_identity`

**Build:** `lake build RadialPolynomial` — ✅ clean, no warnings  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`.

### Theorem statement unchanged

Matches proof-capsule.md SLICE-OL-06 section exactly.

### Semantic match

**Intent:** Zero k coefficients → R = 1.  
**Formal conclusion:** `radialTerm k r h = 1`.  
After `simp only [radialTerm_eq, hk1..hk6]`, both numerator and denominator reduce to `1 + 0 + 0 + 0 = 1`; `norm_num` closes `1 / 1 = 1`. The conclusion is exactly the paper claim.

**Non-vacuity:** With k1 = 1, `radialTerm k r h = (1 + r²) / 1 ≠ 1` for r ≠ 0. The theorem genuinely requires all six zero hypotheses.

### Proof structure

- `simp only [radialTerm, hk1, hk2, hk3, hk4, hk5, hk6]` — unfolds `radialTerm` and substitutes zeros; Lean's built-in ring simplification reduces the sums to 1.
- `norm_num` — closes `(1 : ℝ) / 1 = 1`.

**Note:** Initial proof used `radialTerm_eq` as a rewrite lemma. That theorem was removed (trivial tautology added speculatively); replaced with direct `simp only [radialTerm, ...]`. Also removed `mul_zero`/`add_zero` after linter reported them unused.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Hidden sorry | ✅ None |
| Vacuous theorem | ✅ Non-vacuous (fails for non-zero k1) |
| `h` parameter dropped to avoid domain obligation | ✅ Explicit `h` present |
| Unused simp lemmas | ✅ Cleaned up after linter warning |
| Wrong coefficient role (num/den swap) | ✅ Correct — k1,k3,k5 zeroed in numerator; k2,k4,k6 zeroed in denominator |

---

## SLICE-OL-07 — `undistortX`, `undistortY`, `undistortPoint`

**Build:** `lake build DistortionModel` — ✅ clean  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`. Definition-only slice.

### Definition match to paper

| Definition | Paper equation | Match |
|---|---|---|
| `undistortX` | §4.1 Eq (16): R·ϵ_x + 2p1·ϵ_x·ϵ_y + p2·(r²+2ϵ_x²) | ✅ Exact |
| `undistortY` | §4.1 Eq (16): R·ϵ_y + p1·(r²+2ϵ_y²) + 2p2·ϵ_x·ϵ_y | ✅ Exact |
| `undistortPoint` | U(ϵ) = (U_x, U_y) | ✅ Packages x and y |

### Domain predicate threading

`h : denominatorNonzero k (sensorRadius ε)` is forwarded to `radialTerm` in both
`undistortX` and `undistortY`. No new nonzero evidence is created inside the definitions.
The predicate obligation is visible at every call site.

### Component form audit (AMB-OL-004)

The diagonal matrix form U(ϵ) = diag(R,R)·ϵ + tangential_terms from the paper is
algebraically equivalent to the component form defined here. The choice of component form
is intentional — it avoids matrix infrastructure and keeps all expressions in ℝ for direct
use with `ring` in downstream proofs.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Matrix form used | ✅ Component form — no matrix types |
| `h` dropped | ✅ Explicit in all three signatures |
| U⁻¹ defined prematurely | ✅ Not present — deferred to OL-DEFER-03 |
| Wrong tangential formula | ✅ p1/p2 placement matches Eq (16): p1 on cross terms and y², p2 on cross terms and x² |
