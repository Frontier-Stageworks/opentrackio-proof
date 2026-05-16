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

---

## Pending review (deferred)

All remaining mutations. Each will be added here upon completion and verification.
