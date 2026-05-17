---
name: pixel-equivalence-proof-plan
description: Adopted proof plan for PixelEquivalence.lean — reconstructed from existing proof bodies
metadata:
  type: project
---

# Proof Plan — PixelEquivalence.lean (Adopted)

This document reconstructs the proof plan from the existing proof bodies.
It is written for future maintainability, not as a prospective plan.

---

## Theorem 1: `linear_projection_pixel_equivalence_2d_iff`

### Goal shape

An iff between a universal quantification over (x, y) and a four-part conjunction.

### Proof strategy

**Theorem delegation** — the proof body is a single term:

```lean
principal_point_conversion_2d_iff
  w h w_shader h_shader fx fy cx cy F ΔPx ΔPy hw hh hw_s hh_s
```

The theorem statement is definitionally equal to `principal_point_conversion_2d_iff` instantiated with the same variables. No tactic work is needed.

### Opening move

Direct application: pass all parameters to the existing theorem. The statement serves as a named alias in pipeline vocabulary — `x` and `y` instead of `x''` and `y''`.

### Hard step

None. The full proof burden is discharged by `principal_point_conversion_2d_iff`.

### Automation budget

Zero. Term-mode proof.

---

## Theorem 2: `radial_distortion_value_equivalence`

### Goal shape

A conjunction of two claims:
1. Two division expressions are equal.
2. The second denominator is nonzero.

### Proof strategy

**Equality transport + field normalization**:

1. Derive power nonzero-ness: `hF2`, `hF4`, `hF6` from `pow_ne_zero _ hF`.
2. Prove numerator equality `hnum`: substitute `hl1, hl3, hl5` then `field_simp [hF2, hF4, hF6]` cancels the `F^(2n)` factors from `(ki/F^(2n)) * (F*r)^(2n) = ki*r^(2n)`.
3. Prove denominator equality `hden`: same pattern with `hl2, hl4, hl6`.
4. Derive `hden_oti` from `hden ▸ hden_cv`: Lean's `▸` rewrites the type of `hden_cv` along `hden`, transporting the `≠ 0` proof.
5. Close with `⟨by rw [hnum, hden], hden_oti⟩`.

### Opening move

```lean
have hF2 : F^2 ≠ 0 := pow_ne_zero _ hF
have hF4 : F^4 ≠ 0 := pow_ne_zero _ hF
have hF6 : F^6 ≠ 0 := pow_ne_zero _ hF
```

**Why:** `field_simp` needs these to discharge division side conditions when clearing `F^(2n)` from `ki/F^(2n)`.

### Hard step

The `field_simp [hF2, hF4, hF6]` calls after `rw [hli, hlj, hlk]`. This must simplify:

```
(ki / F^(2n)) * (F * r)^(2n) → ki * r^(2n)
```

for each term, then close the equality by normalization. The fact that `field_simp` alone (without a trailing `ring`) closes these goals means field_simp fully normalizes both sides to the same expression.

The `hden ▸ hden_cv` transport is the other notable step: it is not arithmetic but a type-level rewrite. This is the cleanest way to transfer `≠ 0` along a propositional equality.

### Automation budget

- `pow_ne_zero`: exact
- `rw`: explicit rewrites
- `field_simp [hF2, hF4, hF6]`: field normalization (closes numerator and denominator equality goals)
- `hden ▸ hden_cv`: propositional rewrite
- No `nlinarith`, no `ring`, no `simp` without explicit lemmas

### If field_simp stops closing the goal in a future Mathlib upgrade

Fallback: add `ring` after `field_simp`. The normalization target is known: `ki * r^(2n)` after cancelling `F^(2n)`, so `ring` will close any reordering residual.
