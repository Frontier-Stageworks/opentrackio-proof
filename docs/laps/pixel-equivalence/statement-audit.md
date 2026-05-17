---
name: pixel-equivalence-statement-audit
description: Statement audit for PixelEquivalence.lean — adopted proof
metadata:
  type: project
---

# Statement Audit — PixelEquivalence.lean (Adopted)

---

## Theorem 1: `linear_projection_pixel_equivalence_2d_iff`

### Formal statement

```lean
theorem linear_projection_pixel_equivalence_2d_iff
    (w h w_shader h_shader fx fy cx cy F ΔPx ΔPy : ℝ)
    (hw   : w ≠ 0) (hh   : h ≠ 0)
    (hw_s : w_shader ≠ 0) (hh_s : h_shader ≠ 0) :
    (∀ x y : ℝ,
        fx * x + cx = (w_shader / w) * (F * x + ΔPx) + w_shader / 2 ∧
        fy * y + cy = (h_shader / h) * (F * y + ΔPy) + h_shader / 2) ↔
    F   = (w / w_shader) * fx  ∧
    ΔPx = (w / w_shader) * (cx - w_shader / 2) ∧
    F   = (h / h_shader) * fy  ∧
    ΔPy = (h / h_shader) * (cy - h_shader / 2)
```

### Plain English

The 2D linear projection from OpenCV (u = fx·x + cx; v = fy·y + cy) and from OpenTrackIO (u = (ws/w)·(F·x + ΔPx) + ws/2; v = (hs/h)·(F·y + ΔPy) + hs/2) agree at every input point (x, y) if and only if the four published conversion formulas hold.

### Comparison to intended claim

The file header states: "The linear (pinhole) projection is identical in both models for all input points iff the published principal-point and focal-length conversions hold." Statement matches perfectly. The iff direction is both necessary and sufficient.

### Audit checks

| Check | Result |
|-------|--------|
| Vacuous? | No — both directions are inhabited; witness for ← is the formulas themselves |
| Over-strong hypotheses? | `hw`, `hh`, `hw_s`, `hh_s` are all required (denominators in the conversion formulas) |
| Unused hypotheses? | None |
| Weakened conclusion? | No — iff is the strongest possible form |
| Proxy property? | No — directly states pixel coordinate equality for all points |
| Unreadable spec? | No — reads clearly as the camera model consistency condition |
| Statement laundering? | No — this is a named re-export of `principal_point_conversion_2d_iff` in pipeline vocabulary, not a weakening |

### Classification

**Accepted as-is.** The theorem is well-stated, matches intent, and is the strongest possible form (iff).

---

## Theorem 2: `radial_distortion_value_equivalence`

### Formal statement

```lean
theorem radial_distortion_value_equivalence
    (k1 k2 k3 k4 k5 k6 l1 l3 l5 l2 l4 l6 F r : ℝ)
    (hF  : F ≠ 0)
    (hl1 : l1 = k1 / F^2) (hl3 : l3 = k2 / F^4) (hl5 : l5 = k3 / F^6)
    (hl2 : l2 = k4 / F^2) (hl4 : l4 = k5 / F^4) (hl6 : l6 = k6 / F^6)
    (hden_cv : 1 + k4*r^2 + k5*r^4 + k6*r^6 ≠ 0) :
    (1 + k1*r^2 + k2*r^4 + k3*r^6) / (1 + k4*r^2 + k5*r^4 + k6*r^6) =
    (1 + l1*(F*r)^2 + l3*(F*r)^4 + l5*(F*r)^6) /
    (1 + l2*(F*r)^2 + l4*(F*r)^4 + l6*(F*r)^6) ∧
    1 + l2*(F*r)^2 + l4*(F*r)^4 + l6*(F*r)^6 ≠ 0
```

### Plain English

Given the six coefficient conversions (li = ki / F^(2n) for n = 1, 2, 3), at any radius pair (r in OpenCV, F·r in OpenTrackIO):

1. The rational radial scale factors are equal: the fraction (1 + k1·r² + k2·r⁴ + k3·r⁶) / (1 + k4·r² + ...) equals the corresponding OpenTrackIO fraction at r_u = F·r.
2. The OpenTrackIO denominator is nonzero whenever the OpenCV denominator is.

The r variable is universally quantified implicitly (it is a free parameter, not universally quantified in the statement — the theorem is about a specific r).

### Comparison to intended claim

The file header states: "The rational radial scale factor has the same value in both models at corresponding radii." Statement matches. The bonus second conjunct (denominator nonzero-ness transport) is a useful corollary that confirms the OTI quotient is well-defined.

### Audit checks

| Check | Result |
|-------|--------|
| Vacuous? | No — satisfiable with F=1, ki arbitrary, r=0 (denominator = 1 ≠ 0) |
| Over-strong hypotheses? | `hF` needed for field_simp; all six `hli` needed for substitution; `hden_cv` needed for second conjunct. All necessary |
| Unused hypotheses? | None |
| Weakened conclusion? | No — the one-way implication is correct here (the paper documents this as a corollary of coefficient conversion, not an iff) |
| Proxy property? | No — rational factor equality is the exact semantic claim |
| Unreadable spec? | Slightly dense due to six coefficient hypotheses, but matches the paper's parameter list directly |
| Statement laundering? | No — this is original content not delegated from an existing iff |

### Note on hypothesis interface design

The theorem takes individual coefficient equations (hl1...hl6) as hypotheses rather than the universal polynomial consistency. This is a deliberate, correct design choice:

- It makes the theorem composable with `all_distortion_conversions_iff` (which produces exactly these equations) without requiring `DistortionConversion` to be imported.
- It avoids importing `DistortionConversion` for what is fundamentally a statement about rational function evaluation, not about polynomial consistency.
- It is strictly weaker in hypotheses than taking the polynomial consistency — i.e., the theorem is stronger.

### Classification

**Accepted as-is.** Well-stated. The one-way implication (→ only, no iff) is correct given the paper's scope. The interface design (individual coefficient equations) is intentional and sound.
