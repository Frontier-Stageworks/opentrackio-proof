---
name: principal-point-conversion-proof-plan
description: Adopted proof plan for PrincipalPointConversion.lean — reconstructed from existing proof bodies
metadata:
  type: project
---

# Proof Plan — PrincipalPointConversion.lean (Adopted)

Reconstructed from existing proof bodies for future maintainability.

---

## Theorem 1: `principal_point_conversion_necessary`

### Goal shape

A conjunction: `F = ... ∧ ΔPx = ...`, both to be derived from the universal hypothesis `hconsist`.

### Proof strategy

**Point specialisation + linear system**

The key insight: the consistency equation `fx * x'' + cx = (w_shader / w) * (F * x'' + ΔPx) + w_shader / 2` is an affine function of x''. Two point specialisations give a 2×2 linear system that uniquely determines F and ΔPx.

### Opening move

```lean
have h0 := hconsist 0
have h1 := hconsist 1
```

**Why:** x'' = 0 isolates the intercept (ΔPx and cx), x'' = 1 adds the slope (F and fx). Together they give two independent linear equations in two unknowns.

### Step-by-step

1. `simp only [mul_zero, zero_add, mul_one] at h0 h1` — simplify the x''=0 and x''=1 instances
2. `field_simp [hw, hw_s] at h0 h1` — clear all division, giving two polynomial equations:
   - h0 : `cx * w * 2 = w_shader * ΔPx * 2 + w_shader * w` (intercept)
   - h1 : `(fx + cx) * w * 2 = w_shader * (F + ΔPx) * 2 + ...` (slope + intercept)
3. `constructor`
4. `· field_simp [hw, hw_s]; nlinarith` — F equation from h1 - h0
5. `· field_simp [hw, hw_s]; nlinarith` — ΔPx equation from h0

### Hard step

`nlinarith` closing each goal after `field_simp`. The system is linear but the variables appear as products after clearing denominators (e.g. `w_shader * F`), so `nlinarith` is needed rather than `linarith`. The key: `h1 - h0` isolates the F term; `h0` alone determines ΔPx.

### Automation budget

- `field_simp`: deterministic, clears denominators
- `nlinarith`: needed once per component; both goals are linear-arithmetic after `field_simp`

---

## Theorem 2: `principal_point_conversion_iff`

### Goal shape

An iff between a universally quantified equation and a conjunction.

### Proof strategy

**Constructor pair** — pair the necessity direction (Theorem 1) with an explicit sufficiency witness.

```lean
⟨principal_point_conversion_necessary w w_shader fx cx F ΔPx hw hw_s,
 fun ⟨hF, hΔPx⟩ x'' => by rw [hF, hΔPx]; field_simp [hw, hw_s]; ring⟩
```

### Hard step

The ← direction: given `hF` and `hΔPx`, verify consistency for all x'' by `rw; field_simp; ring`. The ring solver closes the algebraic identity after substitution and division clearing.

---

## Theorem 3: `principal_point_conversion_2d_iff`

### Goal shape

An iff between a 2D universal quantification and a four-part conjunction.

### Proof strategy

**Axis decomposition** — reduce 2D to two independent 1D problems using Theorem 2.

### Opening move (→ direction)

```lean
have hx : ∀ x'' : ℝ, ... := fun x'' => (hconsist x'' 0).1
have hy : ∀ y'' : ℝ, ... := fun y'' => (hconsist 0 y'').2
```

**Why:** Specialising at y''=0 gives a hypothesis depending only on x'' (the x-component), and specialising at x''=0 gives one depending only on y''. This is the key decomposition — the two axes are independent in the affine model.

### Hard step

The decomposition `(hconsist x'' 0).1` — recognising that the y component at y''=0 decouples. The ← direction reconstructs by applying Theorem 2 to each axis independently.

### Automation budget

`obtain` + term-mode application of Theorem 2 twice. No arithmetic solvers needed.

---

## Theorem 4: `single_focal_length_compatibility`

### Goal shape

`(w / w_shader) * fx = (h / h_shader) * fy` — a linear equality between the two F expressions.

### Proof strategy

**Delegation + linarith**

Apply Theorem 3 to `hconsist`, destructure the four-part conjunction, and use `linarith` since both expressions equal F.

```lean
obtain ⟨hFx, _, hFy, _⟩ :=
  (principal_point_conversion_2d_iff ...).mp hconsist
linarith
```

**Why linarith:** `hFx : F = (w/w_shader)*fx` and `hFy : F = (h/h_shader)*fy` give the conclusion by transitivity — `(w/w_shader)*fx = F = (h/h_shader)*fy`. `linarith` handles this as `hFx.symm ▸ hFy` expressed linearly.

### Hard step

None — `linarith` closes immediately from the two equalities.

---

## Theorem 5: `buggy_principal_point_conversion_inconsistent`

### Goal shape

`False` — derive a contradiction.

### Proof strategy

**Contradiction via scale nonzero-ness**

1. Apply Theorem 1 to get `hΔPx : ΔPx = (w / w_shader) * (cx - w_shader / 2)`
2. Combine with `hbug : ΔPx = (w / w_shader) * cx` to derive `(w / w_shader) * (w_shader / 2) = 0`
3. Since `w / w_shader ≠ 0` (from `div_ne_zero hw hw_s`), the product being zero forces `w_shader / 2 = 0`, i.e. `w_shader = 0`
4. This contradicts `hw_s`

### Key algebraic identity

From `(w/w_shader)*cx = (w/w_shader)*(cx - w_shader/2)`:
- Subtract: `(w/w_shader) * (w_shader/2) = 0`
- Since scale is nonzero: `w_shader/2 = 0` → `w_shader = 0`

### Hard step

The `mul_eq_zero.mp hws2` case split: the product is zero iff one factor is zero. The `hscale_ne` hypothesis immediately closes the first case; the second case uses `linarith` to get `w_shader = 0`.

### Automation budget

- `div_ne_zero hw hw_s` — exact
- `linarith` — closes `hws2` from `hΔPx` and `hbug`
- `mul_eq_zero.mp` — exact
- `rcases` — structural case split
- `absurd h hscale_ne` — exact
- `linarith` — closes `w_shader = 0` from `h : w_shader / 2 = 0`
