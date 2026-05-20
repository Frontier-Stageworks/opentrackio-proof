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
