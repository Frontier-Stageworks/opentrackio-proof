---
name: mutation-tests-proof-review
description: Proof review for MutationTests.lean — updated incrementally as theorems are completed
metadata:
  type: project
---

# Proof Review — MutationTests.lean

## Completed theorems

### wrong_projection_offset_unscaled_forces_degenerate_relation

**Classification:** Forces degeneracy

**Existing iff theorem used:** `principal_point_conversion_necessary`
(returns conjunction; `.2` component gives `ΔPx = (w/w_shader)*(cx - w_shader/2)`)

**Anti-degeneracy assumptions used:** None — this is the degeneracy layer only.
The contradiction layer (`wrong_projection_offset_unscaled_inconsistent`) is deferred.

**Overclaims?** No. The conclusion is exactly what consistency forces when `ΔPx = cx`.
It does not claim `False`; it claims a necessary equality on cx.

**Contributes to confidence?** Yes — confirms that `principal_point_conversion_necessary`
is strong enough to derive the ΔPx formula from consistency alone, without baking
the formula into a definition.

### buggy_projection_offset_missing_center_inconsistent

**Classification:** Direct contradiction

**Existing theorem used:** `buggy_principal_point_conversion_inconsistent` (PrincipalPointConversion)

**Anti-degeneracy assumptions:** `w ≠ 0`, `w_shader ≠ 0` (sufficient for unconditional contradiction)

**Overclaims?** No — the existing theorem already established this is unconditional.

---

### wrong_projection_offset_unscaled_inconsistent

**Classification:** Contradiction under anti-degeneracy

**Anti-degeneracy assumption:** `cx ≠ (w / w_shader) * (cx - w_shader / 2)` — exactly the negation of the layer-1 forced equality.

**Proof:** Calls layer-1 theorem, applies `hnot`. No algebra.

**Overclaims?** No.

---

### wrong_projection_offset_minus_half_forces_degenerate_relation

**Classification:** Forces degeneracy

**Existing iff theorem used:** `principal_point_conversion_necessary`

**What is forced:** `cx - w_shader / 2 = (w / w_shader) * (cx - w_shader / 2)` — the principal-point offset must be a fixed point of the scale factor.

**Overclaims?** No — wrong formula is satisfiable (e.g. w = w_shader makes it trivially true). Correctly does not claim `False`.

---

### wrong_projection_offset_minus_half_inconsistent

**Classification:** Contradiction under anti-degeneracy

**Anti-degeneracy assumption:** `cx - w_shader / 2 ≠ (w / w_shader) * (cx - w_shader / 2)` — single minimal negation.

**Overclaims?** No.

---

## Pending review (deferred)

All remaining mutations. Each will be added here upon completion and verification.
