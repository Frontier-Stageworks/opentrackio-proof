---
name: distortion-conversion-proof-plan
description: Adopted proof plan for DistortionConversion.lean — reconstructed from existing proof bodies
metadata:
  type: project
---

# Proof Plan — DistortionConversion.lean (Adopted)

Reconstructed from existing proof bodies for future maintainability.

---

## Theorem 1: `radial_distortion_conversion`

### Goal shape

`l = k / F ^ (2 * n)` — a single coefficient equality, to be derived from the universal hypothesis.

### Proof strategy

**Point specialisation + field normalisation**

Specialise at `r = 1`. After simplification, the hypothesis gives `k = l * F^(2n)`. Clear denominators and close linearly.

### Step-by-step

1. `have h1 := hconsist 1` — specialise
2. `simp only [mul_one, one_pow] at h1` — simplify: `k * 1 = l * F^(2n) * 1` → `k = l * F^(2n)`
3. `have hFn : F ^ (2 * n) ≠ 0 := pow_ne_zero _ hF`
4. `field_simp [hFn]` — clear denominator in goal `l = k / F^(2n)` → `l * F^(2n) = k`
5. `linarith` — closes from h1

### Hard step

`pow_ne_zero _ hF` producing `hFn` to enable `field_simp`. Without it, `field_simp` cannot clear the `F^(2n)` denominator. After clearing, the system is 1-variable linear and `linarith` closes immediately.

---

## Theorem 2: `tangential_q1_conversion`

### Goal shape

`q1 = p1 / F ^ 2` — single coefficient equality.

### Proof strategy

**Point specialisation + nlinarith**

Specialise at `(x', y') = (1, 1)`.

### Step-by-step

1. `have h11 := hconsist 1 1`
2. `simp only [mul_one] at h11` — gives `p1 = q1 * F * F`
3. `have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF`
4. `field_simp [hF2]` — normalise goal
5. `nlinarith [sq_nonneg F]` — close; `sq_nonneg F` provides `0 ≤ F^2` to orient the quadratic

### Hard step

`nlinarith [sq_nonneg F]` — after `field_simp` the goal involves `F^2` products; `sq_nonneg F` is the key hint that lets nlinarith close rather than `linarith` (which would not handle the quadratic factor).

---

## Theorem 3: `tangential_q2_conversion`

### Goal shape

`q2 = p2 / F ^ 2` — single coefficient equality.

### Proof strategy

**Point specialisation + nlinarith**

Specialise at `(r, x') = (1, 0)`. Cross term `2*x'^2 = 0` vanishes, leaving a pure radial equation.

### Step-by-step

1. `have h10 := hconsist 1 0`
2. `simp only [mul_zero, sq, mul_one, add_zero] at h10` — simplify to `p2 = q2 * F^2`
3. `have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF`
4. `field_simp [hF2]`
5. `nlinarith [sq_nonneg F]`

### Hard step

Same pattern as Theorem 2: `nlinarith [sq_nonneg F]` after `field_simp`.

---

## Theorem 4: `whole_radial_polynomial_iff`

### Goal shape

An iff between a universally quantified polynomial equality and a three-part conjunction.

### Proof strategy

**Vandermonde point specialisation (→) + rewrite (←)**

The key insight: the polynomial `a1*r^2 + a2*r^4 + a3*r^6 = 0` for all `r`, where `ai = ki - li*F^(2i)`. Three specialisations `r = 1, 2, 3` give a 3×3 system with Vandermonde-like matrix (entries 1, 4, 9 in the r^2 row), which has nonzero determinant. `nlinarith` closes all three component goals simultaneously.

### Step-by-step (→)

1. `intro h; have h1 := h 1; have h2 := h 2; have h3 := h 3`
2. `simp only [one_pow, mul_one] at h1`
3. `norm_num at h2 h3` — evaluate powers: h2 has 4, 16, 64; h3 has 9, 81, 729
4. `refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> nlinarith`

### Step-by-step (←)

1. `intro ⟨hl1, hl3, hl5⟩ r`
2. `rw [hl1, hl3, hl5]`
3. `field_simp` — verifies algebraic identity

### Hard step (→)

`norm_num at h2 h3` is the key preprocessing step — it evaluates the concrete powers so `nlinarith` sees a fully numeric linear system. Without `norm_num`, nlinarith would face symbolic power terms it cannot compare.

The `<;>` usage is valid: the three subgoals produced by `refine ⟨?_, ?_, ?_⟩` all have the form `l_i = k_j / F^(2i)` and each closes by the same `field_simp; nlinarith` chain using h1, h2, h3 in context.

### Automation budget

- `norm_num`: deterministic evaluation of h2, h3
- `field_simp`: deterministic denominator clearing
- `nlinarith`: closes each of three linear-after-field_simp goals; the three specialisations provide sufficient constraints

---

## Theorem 5: `whole_tangential_field_iff`

### Goal shape

An iff between a universally quantified tangential equality and a two-part conjunction.

### Proof strategy

**Overdetermined specialisation (→) + rewrite (←)**

Three specialisations at `(0,1)`, `(1,0)`, `(1,1)`. At `(0,1)` the cross term `p1*x'*y'` vanishes (x'=0), isolating q2. At `(1,1)` both terms contribute, allowing q1 to be determined once q2 is known. The system is overdetermined (3 equations, 2 unknowns) but consistent — `nlinarith` closes both goals.

### Step-by-step (→)

1. `intro h; have h01 := h 0 1; have h10 := h 1 0; have h11 := h 1 1`
2. `simp only [mul_zero, zero_mul, mul_one, zero_add] at h01 h10 h11`
3. `norm_num at h01 h10 h11`
4. `refine ⟨?_, ?_⟩ <;> field_simp <;> nlinarith`

### Hard step

`norm_num at h01 h10 h11` — evaluates the concrete specialisations to numeric form. `nlinarith` then handles the two remaining goals (q1, q2) using the overdetermined system.

### Automation budget

Same pattern as Theorem 4.

---

## Theorem 6: `whole_tangential_field_2d_iff`

### Goal shape

An iff between a 2D universal quantification (both δx and δy) and a two-part conjunction.

### Proof strategy

**Delegation to Theorem 5 + ring (←)**

The → direction extracts δx and applies `whole_tangential_field_iff`. The ← direction applies Theorem 5 for δx; confirms δy by `rw + field_simp`.

### Step-by-step (→)

```lean
apply (whole_tangential_field_iff p1 p2 q1 q2 F hF).mp
intro x' y'
exact (h x' y').1
```

The key insight: `.1` extracts the δx component. δx alone determines both q1 and q2.

### Step-by-step (←)

```lean
intro ⟨hq1, hq2⟩ x' y'
constructor
· exact (whole_tangential_field_iff p1 p2 q1 q2 F hF).mpr ⟨hq1, hq2⟩ x' y'
· rw [hq1, hq2]; field_simp
```

### Hard step

None — the → direction is a clean single-component extraction and delegation. The ← direction's δy verification is mechanical: `rw + field_simp` confirms the algebraic identity.

---

## Theorem 7: `all_distortion_conversions_iff`

### Goal shape

An iff between a three-component conjunction (both radial polynomials + 2D tangential field) and an eight-part flat conjunction.

### Proof strategy

**Delegation + conjunction rearrangement**

Rewrite the LHS using three iff theorems (Theorems 4, 4 again, 6), converting each component to its coefficient form. The resulting goal is just conjunction rearrangement: flatten nested triples and pairs into a flat 8-tuple.

### Opening move

```lean
rw [whole_radial_polynomial_iff k1 k2 k3 l1 l3 l5 F hF,
    whole_radial_polynomial_iff k4 k5 k6 l2 l4 l6 F hF,
    whole_tangential_field_2d_iff p1 p2 q1 q2 F hF]
```

After these three rewrites, the goal is:
`(l1=k1/F^2 ∧ l3=k2/F^4 ∧ l5=k3/F^6) ∧ (l2=k4/F^2 ∧ l4=k5/F^4 ∧ l6=k6/F^6) ∧ (q1=p1/F^2 ∧ q2=p2/F^2)
↔ l1=k1/F^2 ∧ l3=k2/F^4 ∧ l5=k3/F^6 ∧ l2=k4/F^2 ∧ l4=k5/F^4 ∧ l6=k6/F^6 ∧ q1=p1/F^2 ∧ q2=p2/F^2`

### Step-by-step

```lean
constructor
· intro ⟨⟨h1, h3, h5⟩, ⟨h2, h4, h6⟩, hq1, hq2⟩
  exact ⟨h1, h3, h5, h2, h4, h6, hq1, hq2⟩
· intro ⟨h1, h3, h5, h2, h4, h6, hq1, hq2⟩
  exact ⟨⟨h1, h3, h5⟩, ⟨h2, h4, h6⟩, hq1, hq2⟩
```

Pure conjunction restructuring. No arithmetic.

### Hard step

None — this theorem is entirely structural. All arithmetic is delegated to Theorems 4 and 6.

---

## Theorem 8: `radial_coefficients_imply_rational_factor_equality`

### Goal shape

An equality of two division expressions at a fixed `r`.

### Proof strategy

**Linear combination + rewrite**

Add 1 to both `hnum` and `hden` to get numerator and denominator equalities, then rewrite.

### Step-by-step

```lean
have hd_cv : 1 + k4 * r ^ 2 + ... = 1 + l2 * (F * r) ^ 2 + ... := by linarith
have hn_cv : 1 + k1 * r ^ 2 + ... = 1 + l1 * (F * r) ^ 2 + ... := by linarith
rw [hn_cv, hd_cv]
```

### Hard step

None — `linarith` trivially extends `hnum` and `hden` by adding 1. The final `rw` closes by `rfl` (equal expressions rewrite to definitional equality).

### Automation budget

- `linarith` twice (add 1 to hypotheses)
- `rw` (close by congruence)
