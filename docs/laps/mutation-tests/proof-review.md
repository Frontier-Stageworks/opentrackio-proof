---
name: mutation-tests-proof-review
description: Final proof review for MutationTests.lean — all 34 theorems + 2 sanity examples (updated after H.3 addition)
metadata:
  type: project
---

# Proof Review — MutationTests.lean

## Verdict

accepted with notes (H.3 gap closed; `whole_tangential_field_iff` choice confirmed)

## File compiles clean

`lake env lean opencv_opentrackio_proofs/MutationTests.lean` — no output (clean).
No `sorry`, `admit`, `axiom`, `unsafe`, or `partial` in the file.

---

---

## Per-Theorem Classification

Each theorem is classified as one of:
- **DC** — direct contradiction (`False` from wrong formula + well-formedness conditions only; no anti-degeneracy hypothesis)
- **FD** — forces degeneracy (wrong formula + consistency → nontrivial equality)
- **CD** — contradiction under anti-degeneracy (FD + negation of forced equality → `False`)
- **PS** — positive sanity example (satisfiability witness)

| ID | Theorem | Class | Degenerate condition |
|----|---------|-------|----------------------|
| A | `buggy_projection_offset_missing_center_inconsistent` | **DC** | — |
| B.1 | `wrong_projection_offset_unscaled_forces_degenerate_relation` | **FD** | `cx = (w/w_shader)*(cx - w_shader/2)` |
| B.2 | `wrong_projection_offset_unscaled_inconsistent` | **CD** | ↑ |
| C.1 | `wrong_projection_offset_minus_half_forces_degenerate_relation` | **FD** | `cx - w_shader/2 = (w/w_shader)*(cx - w_shader/2)` |
| C.2 | `wrong_projection_offset_minus_half_inconsistent` | **CD** | ↑ |
| D.1 | `wrong_focal_length_identity_forces_degeneracy` | **FD** | `w = w_shader` |
| D.2 | `wrong_focal_length_identity_inconsistent` | **CD** | ↑ |
| E | `wrong_focal_length_inverted_inconsistent` | **CD** | `w = w_shader` (positivity excludes `w = -w_shader`) |
| F.1 | `wrong_l1_power_F4_forces_power_degeneracy` / `_inconsistent` | **FD/CD** | `F^2 = F^4` |
| F.2 | `wrong_l3_power_F2_forces_power_degeneracy` / `_inconsistent` | **FD/CD** | `F^2 = F^4` |
| F.3 | `wrong_l5_power_F4_forces_power_degeneracy` / `_inconsistent` | **FD/CD** | `F^6 = F^4` |
| F.4 | `wrong_l2_power_F4_forces_power_degeneracy` / `_inconsistent` | **FD/CD** | `F^2 = F^4` |
| F.5 | `wrong_l4_power_F2_forces_power_degeneracy` / `_inconsistent` | **FD/CD** | `F^2 = F^4` |
| F.6 | `wrong_l6_power_F4_forces_power_degeneracy` / `_inconsistent` | **FD/CD** | `F^6 = F^4` |
| G.1 | `wrong_q1_power_F1_forces_power_degeneracy` / `_inconsistent` | **FD/CD** | `F^2 = F` |
| G.2 | `wrong_q1_power_F4_forces_power_degeneracy` / `_inconsistent` | **FD/CD** | `F^2 = F^4` |
| G.3 | `wrong_q2_power_F1_forces_power_degeneracy` / `_inconsistent` | **FD/CD** | `F^2 = F` |
| G.4 | `wrong_q2_power_F4_forces_power_degeneracy` / `_inconsistent` | **FD/CD** | `F^2 = F^4` |
| H.1 | `wrong_l1_swapped_k2_forces_equal_coefficients` / `_inconsistent` | **FD/CD** | `k1 = k2` |
| H.2 | `wrong_q1_swapped_p2_forces_equal_coefficients` / `_inconsistent` | **FD/CD** | `p1 = p2` |
| H.3 | `wrong_q2_swapped_p1_forces_equal_coefficients` / `_inconsistent` | **FD/CD** | `p1 = p2` |
| I.1 | `example` (existential witness) | **PS** | — |
| I.2 | `example` (numeric witness) | **PS** | — |

**Confirmation: No theorem is classified DC where only degeneracy is forced.**
- All DC theorems (A, and E once anti-degeneracy is included) genuinely produce `False`.
- All FD theorems conclude with an equality, never `False`.
- All CD theorems explicitly carry the negation of their FD equality as a hypothesis.
- Theorem E is classified CD, not DC: it requires `hne : w ≠ w_shader` to reach `False`.

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
| `wrong_q2_swapped_p1_forces_equal_coefficients` | `q2 = p1/F^2` | `p1 = p2` |

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

## Why `whole_tangential_field_iff` is correct for section G

The G theorems (tangential wrong-power mutations) use `whole_tangential_field_iff` (δx consistency only).
The question is whether they should instead use `whole_tangential_field_2d_iff` (δx AND δy).

**`whole_tangential_field_iff` is the right choice.** The G mutation theorems carry:

```lean
hpoly : ∀ x' y' : ℝ, (δx consistency only)
```

This matches the antecedent of `whole_tangential_field_iff` exactly. Using the 1D theorem means
the hypotheses are **weaker** — the wrong formula is rejected even when only δx consistency is required.
That is a **stronger result**: the wrong formula fails a less demanding test.

Switching to `whole_tangential_field_2d_iff` would require changing every G theorem's `hpoly` to
`∀ x' y', (δx) ∧ (δy)` — a stronger assumption — producing a weaker result (more room for the
wrong formula to be consistent with just one component).

No change is required in section G. The design is intentional and correct.

---

## Existing iff theorems used

| Source theorem | Used in sections |
|---------------|-----------------|
| `principal_point_conversion_necessary` | A, B, C, D, E |
| `buggy_principal_point_conversion_inconsistent` | A (delegation) |
| `whole_radial_polynomial_iff` | F (all 12 radial theorems) |
| `whole_tangential_field_iff` | G (all 8 tangential theorems), H (tangential swaps H.2, H.3) |

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
| H | 6 | Forces coefficient equality + contradiction (3 pairs) |
| I | 2 | Positive sanity examples |
| **Total** | **36** | |

---

## Added theorem: H.3 (`q2 = p1/F^2`)

**Gap closed.** Section H previously covered:
- H.1: radial swap `l1 = k2/F^2` (p2 used as l1 numerator) → forces `k1 = k2`
- H.2: tangential swap `q1 = p2/F^2` (p2 used as q1 numerator) → forces `p1 = p2`

Missing: `q2 = p1/F^2` (p1 used as q2 numerator). The existing comment "one half of the
swap suffices — the other half is symmetric" refers to within-parameter direction symmetry,
not cross-parameter swaps. Using p1 as q2's numerator is a distinct mutation not covered by H.2.

The correct formula gives `q2 = p2/F^2`. Setting `q2 = p1/F^2` and applying
`whole_tangential_field_iff` gives `p2/F^2 = p1/F^2`, hence `p1 = p2` (via
`mul_right_cancel₀` on `F^2`, then `.symm`). Proof follows the H.2 pattern using the
second conjunct `hq2`.

`wrong_q2_swapped_p1_forces_equal_coefficients` and `wrong_q2_swapped_p1_inconsistent`
were added. Lean check passes cleanly.
