---
name: mutation-tests-proof-review
description: Final proof review for MutationTests.lean — all 32 theorems + 2 sanity examples
metadata:
  type: project
---

# Proof Review — MutationTests.lean

## File compiles clean

`lake env lean opencv_opentrackio_proofs/MutationTests.lean` — no output (clean).
No `sorry`, `admit`, `axiom`, `unsafe`, or `partial` in the file.

---

## Which mutations are direct contradictions

| Theorem | Why unconditional |
|---------|------------------|
| `buggy_projection_offset_missing_center_inconsistent` | Missing centering term is incompatible with any nonzero w and w_shader; delegates to `buggy_principal_point_conversion_inconsistent` |
| `wrong_focal_length_inverted_inconsistent` | Under positivity (`w > 0`, `w_shader > 0`) and `w ≠ w_shader`, the inverted scale forces `w² = w_shader²` which implies `w = w_shader`, contradiction; positivity excludes the `w = -w_shader` escape |

---

## Which mutations force degeneracies (layer-1 theorems)

| Theorem | Wrong formula | Forced equality |
|---------|--------------|-----------------|
| `wrong_projection_offset_unscaled_forces_degenerate_relation` | `ΔPx = cx` | `cx = (w/w_shader)*(cx - w_shader/2)` |
| `wrong_projection_offset_minus_half_forces_degenerate_relation` | `ΔPx = cx - w_shader/2` | `cx - w_shader/2 = (w/w_shader)*(cx - w_shader/2)` |
| `wrong_focal_length_identity_forces_degeneracy` | `F = fx` | `w = w_shader` |
| `wrong_l1_power_F4_forces_power_degeneracy` | `l1 = k1/F^4` | `F^2 = F^4` |
| `wrong_l3_power_F2_forces_power_degeneracy` | `l3 = k2/F^2` | `F^2 = F^4` |
| `wrong_l5_power_F4_forces_power_degeneracy` | `l5 = k3/F^4` | `F^6 = F^4` |
| `wrong_l2_power_F4_forces_power_degeneracy` | `l2 = k4/F^4` | `F^2 = F^4` |
| `wrong_l4_power_F2_forces_power_degeneracy` | `l4 = k5/F^2` | `F^2 = F^4` |
| `wrong_l6_power_F4_forces_power_degeneracy` | `l6 = k6/F^4` | `F^6 = F^4` |
| `wrong_q1_power_F1_forces_power_degeneracy` | `q1 = p1/F` | `F^2 = F` |
| `wrong_q1_power_F4_forces_power_degeneracy` | `q1 = p1/F^4` | `F^2 = F^4` |
| `wrong_q2_power_F1_forces_power_degeneracy` | `q2 = p2/F` | `F^2 = F` |
| `wrong_q2_power_F4_forces_power_degeneracy` | `q2 = p2/F^4` | `F^2 = F^4` |
| `wrong_l1_swapped_k2_forces_equal_coefficients` | `l1 = k2/F^2` | `k1 = k2` |
| `wrong_q1_swapped_p2_forces_equal_coefficients` | `q1 = p2/F^2` | `p1 = p2` |

Each forced equality is geometrically meaningful: power degeneracies (`F^a = F^b`) only hold at `F = 0` (excluded), `F = ±1`, or `F = 1` depending on the exponents. Coefficient equalities hold only when two physically distinct parameters are identical.

---

## Anti-degeneracy assumptions used (layer-2 theorems)

Each layer-2 theorem adds exactly the negation of its layer-1 forced equality:

| Theorem cluster | Anti-degeneracy hypothesis |
|----------------|--------------------------|
| Projection offset (B, C) | `cx ≠ (w/w_shader)*(cx - w_shader/2)` or `cx - w_shader/2 ≠ (w/w_shader)*(cx - w_shader/2)` |
| Focal length identity (D) | `w ≠ w_shader` |
| Focal length inverted (E) | `w ≠ w_shader` (combined with positivity — no separate layer needed) |
| Radial wrong-power (F) | `F^2 ≠ F^4` or `F^6 ≠ F^4` |
| Tangential wrong-power (G) | `F^2 ≠ F` or `F^2 ≠ F^4` |
| Coefficient swaps (H) | `k1 ≠ k2` or `p1 ≠ p2` |

All anti-degeneracy hypotheses are the minimal negation of the forced equality. No additional assumptions were added.

---

## Existing iff theorems used

| Source theorem | Used in sections |
|---------------|-----------------|
| `principal_point_conversion_necessary` | A, B, C, D, E |
| `buggy_principal_point_conversion_inconsistent` | A (delegation) |
| `whole_radial_polynomial_iff` | F (all 12 radial theorems) |
| `whole_tangential_field_iff` | G (all 8 tangential theorems), H (tangential swap) |

No positive theorems were reproved from scratch.

---

## Why no mutation theorem overclaims

1. **Forces-degeneracy theorems** do not claim `False`. They claim a specific equality that is satisfied by special-case inputs (e.g. `F = 1` satisfies `F^2 = F^4`; `w = w_shader` satisfies `wrong_focal_length_identity`).

2. **Contradiction theorems** add exactly one anti-degeneracy hypothesis. Removing that hypothesis makes the theorem false in general, confirming the hypothesis is necessary.

3. **Vacuity check**: the positive sanity examples (I.1, I.2) confirm the consistency hypotheses are jointly satisfiable under the correct formulas. If they were not, all mutation theorems would hold vacuously.

4. **Delegation**: theorem A delegates to the existing `buggy_principal_point_conversion_inconsistent` rather than reproving. This makes A's strength exactly equal to the existing theorem — no hidden weakening.

---

## Why the file increases confidence in the existing proof suite

- The positive iff theorems (`principal_point_conversion_iff`, `whole_radial_polynomial_iff`, `whole_tangential_field_iff`) are used as black boxes. Each mutation test is a corollary: if those iff theorems were wrong (e.g. had vacuous hypotheses or proved a proxy property), the mutation theorems would fail to compile or would require different anti-degeneracy assumptions.

- Every wrong formula tested here was either taken from the paper's erratum history or from systematic off-by-one perturbations of the correct formula. The fact that each is rejected — either unconditionally or under a meaningful anti-degeneracy assumption — confirms the positive theorems are not circular definitions.

- The sanity examples confirm non-vacuity: the correct formulas genuinely satisfy the consistency condition, so the mutation tests are testing real mathematical content, not vacuously true statements.

---

## Theorem count

| Section | Theorems | Classification |
|---------|----------|----------------|
| A | 1 | Direct contradiction |
| B | 2 | Forces degeneracy + contradiction |
| C | 2 | Forces degeneracy + contradiction |
| D | 2 | Forces degeneracy + contradiction |
| E | 1 | Direct contradiction (positivity) |
| F | 12 | Forces power degeneracy + contradiction (6 pairs) |
| G | 8 | Forces power degeneracy + contradiction (4 pairs) |
| H | 4 | Forces coefficient equality + contradiction (2 pairs) |
| I | 2 | Positive sanity examples |
| **Total** | **34** | |
