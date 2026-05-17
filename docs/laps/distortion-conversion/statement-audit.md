---
name: distortion-conversion-statement-audit
description: Statement audit for DistortionConversion.lean — adopted proof
metadata:
  type: project
---

# Statement Audit — DistortionConversion.lean (Adopted)

---

## Theorem 1: `radial_distortion_conversion`

### Formal statement

```lean
theorem radial_distortion_conversion
    (k l F : ℝ) (n : ℕ)
    (hF : F ≠ 0)
    (hconsist : ∀ r : ℝ, k * r ^ (2 * n) = l * (F * r) ^ (2 * n)) :
    l = k / F ^ (2 * n)
```

### Plain English

If two single-term distortion contributions `k*r^(2n)` and `l*(F*r)^(2n)` agree for every radius `r`, then `l` must equal `k/F^(2n)`. Valid for any natural number `n`, including `n=0` (which forces `l = k`).

### Audit

| Check | Result |
|-------|--------|
| Vacuous? | No — hconsist is satisfiable for any nonzero F; witnesses exist |
| Over-strong hypotheses? | `hF` is justified by `F^(2n)` appearing in the denominator of the conclusion |
| Unused hypotheses? | None |
| Weakened conclusion? | No — the conclusion is the exact coefficient conversion |
| Proxy property? | No |
| Test-shaped? | No — universally quantified over all r |
| n=0 case? | Valid: n=0 gives `k * 1 = l * 1` → `l = k` (F^0 = 1 makes `k/F^0 = k`); consistent |

### Classification: **Accepted as-is**

---

## Theorem 2: `tangential_q1_conversion`

### Formal statement

```lean
theorem tangential_q1_conversion
    (p1 q1 F : ℝ)
    (hF : F ≠ 0)
    (hconsist : ∀ x' y' : ℝ, p1 * x' * y' = q1 * (F * x') * (F * y')) :
    q1 = p1 / F ^ 2
```

### Plain English

If the cross-term `p1*x'*y'` of the OpenCV tangential model equals the cross-term `q1*(F*x')*(F*y')` of the OpenTrackIO model for all normalised coordinates `(x', y')`, then `q1 = p1/F^2`.

### Audit

| Check | Result |
|-------|--------|
| Vacuous? | No |
| Over-strong hypotheses? | `hF` is justified by `F^2` in the denominator of the conclusion |
| Unused hypotheses? | None |
| Weakened conclusion? | No |
| Proxy property? | No |
| Test-shaped? | No — universally quantified over all x', y' |

### Classification: **Accepted as-is**

---

## Theorem 3: `tangential_q2_conversion`

### Formal statement

```lean
theorem tangential_q2_conversion
    (p2 q2 F : ℝ)
    (hF : F ≠ 0)
    (hconsist : ∀ r x' : ℝ, p2 * (r ^ 2 + 2 * x' ^ 2) = q2 * ((F * r) ^ 2 + 2 * (F * x') ^ 2)) :
    q2 = p2 / F ^ 2
```

### Plain English

If the radial term of the OpenCV tangential model equals the OpenTrackIO version for all `(r, x')`, then `q2 = p2/F^2`.

### Audit

| Check | Result |
|-------|--------|
| Vacuous? | No |
| Over-strong hypotheses? | `hF` is justified; `r` and `x'` are treated as independent variables, which is stronger than the geometric constraint `r^2 = x'^2 + y'^2`. This is correct: polynomial equality for all independent `(r, x')` implies equality under the geometric constraint, and the witness `(r=1, x'=0)` is geometrically realizable. Not over-strong. |
| Unused hypotheses? | None |
| Weakened conclusion? | No |
| Test-shaped? | No — universally quantified over all r, x' |

### Classification: **Accepted as-is**

---

## Theorem 4: `whole_radial_polynomial_iff`

### Formal statement

```lean
theorem whole_radial_polynomial_iff
    (k1 k2 k3 l1 l3 l5 F : ℝ)
    (hF : F ≠ 0) :
    (∀ r : ℝ,
        k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6 =
        l1 * (F * r) ^ 2 + l3 * (F * r) ^ 4 + l5 * (F * r) ^ 6) ↔
    l1 = k1 / F ^ 2 ∧ l3 = k2 / F ^ 4 ∧ l5 = k3 / F ^ 6
```

### Plain English

The full degree-6 radial numerator polynomial is equal for all radii if and only if the three coefficient conversions all hold. This is the strongest possible statement for the three-term radial numerator.

### Audit

| Check | Result |
|-------|--------|
| Vacuous? | No |
| Over-strong hypotheses? | `hF` is justified by `F^2, F^4, F^6` in the denominators |
| Weakened? | No — iff is the strongest form |
| Proxy? | No — conclusion is exactly the parameter conversions |
| `<;>` usage? | `refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> nlinarith` — three subgoals of the same shape, each closed by nlinarith using the three specialisations in context. Not a misuse. |
| Variable naming? | `l1`, `l3`, `l5` (odd-indexed) for OpenTrackIO numerator; `k1`, `k2`, `k3` for OpenCV numerator. Index gap in `l` naming (1,3,5 vs 1,2,3) mirrors the SMPTE paper convention where even-indexed `l` parameters name denominator coefficients. Consistent with `all_distortion_conversions_iff`. |

### Classification: **Accepted as-is**

---

## Theorem 5: `whole_tangential_field_iff`

### Formal statement

```lean
theorem whole_tangential_field_iff
    (p1 p2 q1 q2 F : ℝ)
    (hF : F ≠ 0) :
    (∀ x' y' : ℝ,
        2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2) =
        2 * q1 * (F * x') * (F * y') +
          q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2)) ↔
    q1 = p1 / F ^ 2 ∧ q2 = p2 / F ^ 2
```

### Plain English

The full tangential δx expression agrees for all normalised coordinates if and only if both tangential coefficient conversions hold.

### Audit

| Check | Result |
|-------|--------|
| Vacuous? | No |
| Over-strong hypotheses? | `hF` is justified |
| Weakened? | No — iff |
| Proxy? | No |
| δx only? | Yes — only the x-component of the tangential field is required. This is not a weakening: the x-component alone uniquely determines both q1 and q2. The 2D version (Theorem 6) provides the full vector field formulation. |

### Classification: **Accepted as-is**

---

## Theorem 6: `whole_tangential_field_2d_iff`

### Formal statement

```lean
theorem whole_tangential_field_2d_iff
    (p1 p2 q1 q2 F : ℝ)
    (hF : F ≠ 0) :
    (∀ x' y' : ℝ,
        -- δx
        2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2) =
          2 * q1 * (F * x') * (F * y') +
            q2 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * x') ^ 2) ∧
        -- δy
        p1 * (x' ^ 2 + y' ^ 2 + 2 * y' ^ 2) + 2 * p2 * x' * y' =
          q1 * ((F * x') ^ 2 + (F * y') ^ 2 + 2 * (F * y') ^ 2) +
            2 * q2 * (F * x') * (F * y')) ↔
    q1 = p1 / F ^ 2 ∧ q2 = p2 / F ^ 2
```

### Plain English

The full 2D tangential vector field (both δx and δy components) agrees for all coordinates if and only if both coefficient conversions hold. This is the complete statement — no objection that only half the vector field was formalised.

### Audit

| Check | Result |
|-------|--------|
| Vacuous? | No |
| Over-strong? | Stronger hypothesis (both components) than Theorem 5 (δx only), same conclusion. Not over-strong — the combined requirement is the physically correct one; the theorem shows it gives no additional information beyond δx alone. |
| Weakened? | No — iff |
| Proxy? | No |
| Relationship to Theorem 5? | Theorem 6 delegates to Theorem 5 in the → direction: δx alone is sufficient. Theorem 6 then confirms δy is automatically satisfied in the ← direction. Correct design. |

### Classification: **Accepted as-is**

---

## Theorem 7: `all_distortion_conversions_iff`

### Formal statement

```lean
theorem all_distortion_conversions_iff
    (k1 k2 k3 k4 k5 k6 : ℝ)
    (l1 l2 l3 l4 l5 l6 : ℝ)
    (p1 p2 q1 q2 F : ℝ)
    (hF : F ≠ 0) :
    (∀ r : ℝ, [numerator polynomial equality]) ∧
    (∀ r : ℝ, [denominator polynomial equality]) ∧
    (∀ x' y' : ℝ, [2D tangential field equality]) ↔
    l1 = k1 / F ^ 2 ∧ l3 = k2 / F ^ 4 ∧ l5 = k3 / F ^ 6 ∧
    l2 = k4 / F ^ 2 ∧ l4 = k5 / F ^ 4 ∧ l6 = k6 / F ^ 6 ∧
    q1 = p1 / F ^ 2 ∧ q2 = p2 / F ^ 2
```

### Plain English

The complete distortion model (radial numerator polynomial, radial denominator polynomial, and full 2D tangential vector field) agrees between OpenCV and OpenTrackIO for all coordinates if and only if all eight distortion parameters convert by the `1/F^(2n)` scaling law.

### Audit

| Check | Result |
|-------|--------|
| Vacuous? | No |
| Over-strong? | `hF` is justified; no other hypotheses |
| Weakened? | No — iff, and all eight conversions appear |
| Proxy? | No — conclusion is the exact parameter set |
| Naming note? | `k4,k5,k6` are OpenCV denominator coefficients; `l2,l4,l6` are OpenTrackIO denominator coefficients (even-indexed `l`). `l6 = k6 / F^6` correctly relates the third denominator term. The interleaved naming (odd `l` for numerator, even `l` for denominator) mirrors the SMPTE paper convention. Potentially confusing but consistent throughout the file. |
| 8 parameters? | Yes — l1,l2,l3,l4,l5,l6,q1,q2. Correct. |

### Classification: **Accepted as-is**

---

## Theorem 8: `radial_coefficients_imply_rational_factor_equality`

### Formal statement

```lean
theorem radial_coefficients_imply_rational_factor_equality
    (k1 k2 k3 k4 k5 k6 l1 l3 l5 l2 l4 l6 F : ℝ)
    (r : ℝ)
    (hnum : k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6 =
            l1 * (F * r) ^ 2 + l3 * (F * r) ^ 4 + l5 * (F * r) ^ 6)
    (hden : k4 * r ^ 2 + k5 * r ^ 4 + k6 * r ^ 6 =
            l2 * (F * r) ^ 2 + l4 * (F * r) ^ 4 + l6 * (F * r) ^ 6) :
    (1 + k1 * r ^ 2 + k2 * r ^ 4 + k3 * r ^ 6) /
    (1 + k4 * r ^ 2 + k5 * r ^ 4 + k6 * r ^ 6) =
    (1 + l1 * (F * r) ^ 2 + l3 * (F * r) ^ 4 + l5 * (F * r) ^ 6) /
    (1 + l2 * (F * r) ^ 2 + l4 * (F * r) ^ 4 + l6 * (F * r) ^ 6)
```

### Plain English

If the numerator polynomial terms and denominator polynomial terms match at a fixed radius `r`, then the full rational correction factors are equal at that `r`. (One-way implication — the converse is false in general: equal rational functions can arise from different coefficient sets.)

### Audit

| Check | Result |
|-------|--------|
| Vacuous? | No |
| Over-strong? | No — the two hypotheses are exactly what is needed to add 1 to each side |
| Weakened? | No — one-way is the correct logical direction; the theorem comment documents why the converse is false |
| Fixed r (not ∀r)? | Correct granularity — the theorem is a pointwise consequence; ∀r form is a straightforward corollary but not the intended application |
| No nonzero denominator hypothesis? | Correct — in ℝ, `a/b = c/d` holds syntactically when `a = c` and `b = d` (via `congr_arg₂`), without requiring `b ≠ 0`. The comment in the file documents this explicitly. |
| Proxy? | No |

### Classification: **Accepted as-is**
