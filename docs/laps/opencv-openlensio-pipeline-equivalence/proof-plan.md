---
name: opencv-openlensio-pipeline-equivalence-proof-plan
description: Proof plan for all three pipeline equivalence theorems
metadata:
  type: project
---

# Proof Plan — OpenCV/OpenLensIO Full Pipeline Equivalence

---

## Shared setup facts (used across all three theorems)

### F-scaling of sensorRadius

```lean
have h_radius_scale : sensorRadius ⟨F * ε'.x, F * ε'.y⟩ = F * sensorRadius ε' := by
  simp only [sensorRadius]
  rw [Real.sqrt_eq_iff_sq_eq (by positivity) (by positivity)]
  ring_nf
  rw [Real.sq_sqrt (by positivity)]
  ring
```

Or more directly:
```lean
have h_radius_scale : sensorRadius ⟨F * ε'.x, F * ε'.y⟩ = F * sensorRadius ε' := by
  simp only [sensorRadius]
  rw [show (F * ε'.x)^2 + (F * ε'.y)^2 = F^2 * (ε'.x^2 + ε'.y^2) by ring]
  rw [Real.sqrt_mul (sq_nonneg F), Real.sqrt_sq (le_of_lt hF_pos)]
```

**Why hF_pos is needed**: `Real.sqrt_sq` requires `0 ≤ F`. `hF_pos : 0 < F` provides it.

### r^2 = ε.x^2 + ε.y^2 unfolding

```lean
have h_sq : (sensorRadius ε')^2 = ε'.x^2 + ε'.y^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
```

This lets proofs replace `(sensorRadius ε')^2` with `ε'.x^2 + ε'.y^2`.

### OTI denominator from OpenCV denominator

Given `hden_cv : 1 + k4*(sensorRadius ε')^2 + k5*(sensorRadius ε')^4 + k6*(sensorRadius ε')^6 ≠ 0`
and conversion equations `hl2 : l2 = k4/F^2`, etc.:

```lean
have hden_oti : denominatorNonzero ⟨l1, l2, l3, l4, l5, l6⟩ (sensorRadius ε_screen) := by
  simp only [denominatorNonzero]
  rw [h_radius_scale]
  -- Now the goal is: 1 + l2*(F*r_n)^2 + l4*(F*r_n)^4 + l6*(F*r_n)^6 ≠ 0
  -- Use radial_distortion_value_equivalence's second component
  exact (radial_distortion_value_equivalence k1 k2 k3 k4 k5 k6 l1 l3 l5 l2 l4 l6 F r_n hF
         hl1 hl3 hl5 hl2 hl4 hl6 hden_cv).2
```

(Needs careful instantiation; `r_n = sensorRadius ε'`.)

---

## Theorem 1: opencv_openlensio_radial_pipeline_eq

### Goal shape

```
undistortXCV k1 k2 k3 k4 k5 k6 0 0 ε' hden_cv =
(1/F) * undistortX ⟨l1, l2, l3, l4, l5, l6⟩ TangentialCoefficients.zero ε_screen hden_oti
```

where `ε_screen = ⟨F * ε'.x, F * ε'.y⟩`.

### Opening move

Unfold both sides via `simp only [undistortXCV, undistortX, radialTerm, TangentialCoefficients.zero]`.

After unfolding:
- LHS: `R_cv * ε'.x + 0 + 0`   (tangential terms vanish since p1=p2=0)
  = `(num_cv / den_cv) * ε'.x`
  where `num_cv = 1 + k1*(sensorRadius ε')^2 + k2*(sensorRadius ε')^4 + k3*(sensorRadius ε')^6`
  and   `den_cv = 1 + k4*(sensorRadius ε')^2 + k5*(sensorRadius ε')^4 + k6*(sensorRadius ε')^6`

- RHS: `(1/F) * (R_oti * (F * ε'.x) + 0 + 0)`
  = `R_oti * ε'.x`
  where `R_oti` is the radial term at `sensorRadius ε_screen = F * sensorRadius ε'`

### Hard step

Showing `R_cv = R_oti` after parameter conversion.

Use `radial_distortion_value_equivalence` at `r = sensorRadius ε'`:
```lean
have h_radial :=
  (radial_distortion_value_equivalence k1 k2 k3 k4 k5 k6 l1 l3 l5 l2 l4 l6 F
    (sensorRadius ε') hF hl1 hl3 hl5 hl2 hl4 hl6 hden_cv).1
```

This gives:
```
(1 + k1*r^2 + k2*r^4 + k3*r^6) / (1 + k4*r^2 + k5*r^4 + k6*r^6) =
(1 + l1*(F*r)^2 + l3*(F*r)^4 + l5*(F*r)^6) /
(1 + l2*(F*r)^2 + l4*(F*r)^4 + l6*(F*r)^6)
```

After `rw [h_radius_scale]` (to relate `sensorRadius ε_screen` to `F * sensorRadius ε'`),
the RHS radial term `R_oti` at `sensorRadius ε_screen` becomes exactly the RHS of `h_radial`.

### Closing move

After establishing `R_cv = R_oti`, the goal reduces to:
`R_cv * ε'.x = (1/F) * R_oti * (F * ε'.x)`
= `R_cv * ε'.x = R_oti * ε'.x`   (since `(1/F) * F = 1`, using `hF`)
→ closed by `ring` after `rw [h_radial]`.

### Automation budget

- `simp only [defs]`: unfold
- `rw [h_radius_scale]`: one rewrite
- `radial_distortion_value_equivalence`: exact application
- `ring` or `field_simp [hF]`: close the arithmetic

---

## Theorem 2: opencv_openlensio_full_pipeline_pixel_sufficiency

### Goal shape

```
∀ x' y' : ℝ,
  fx * (R_cv(x'^2+y'^2) * x' + 2*p1*x'*y' + p2*(x'^2+y'^2 + 2*x'^2)) + cx
  =
  (ws/w) * (R_oti(F*r_n) * (F*x') + 2*q1*F*x'*F*y' + q2*((F*r_n)^2 + 2*(F*x')^2) + ΔPx)
  + ws/2
```

where `r_n^2 = x'^2 + y'^2`.

### Opening move

```lean
intro x' y'
```

Then substitute all conversion hypotheses: `hl1, hl3, hl5, hl2, hl4, hl6, hq1, hq2, hF_eq, hΔPx, hscale`.

### Core algebraic computation

After substituting `q1 = p1/F^2`, `q2 = p2/F^2`:
- `2*q1*F*x'*F*y' = 2*(p1/F^2)*F^2*x'*y' = 2*p1*x'*y'`
- `q2*((F*r_n)^2 + 2*(F*x')^2) = (p2/F^2)*(F^2*(x'^2+y'^2) + 2*F^2*x'^2) = p2*(x'^2+y'^2+2*x'^2)`
- So tangential on RHS = tangential on LHS ✓

After substituting `F = (w/ws)*fx`:
- `R_oti(F*r_n) * F*x' = R_cv(r_n) * (w/ws)*fx*x'`
- `(ws/w) * R_cv(r_n) * (w/ws)*fx*x' = fx * R_cv(r_n) * x'` ✓

After substituting `ΔPx = (w/ws)*(cx - ws/2)` and `ws/w = fx`:
- `(ws/w) * ΔPx = (ws/w) * (w/ws)*(cx - ws/2) = cx - ws/2`
- Full OTI = `fx*R_cv*x' + (ws/w)*(2*p1*x'*y' + p2*(...)) + cx - ws/2 + ws/2`
- With `ws/w = fx`: `= fx*R_cv*x' + fx*(tangential) + cx`

This matches the OpenCV pixel output. ✓

### Hard step

The `R_cv = R_oti` substitution. Handle via a `have` using the same approach as Theorem 1:
build `hden_oti` for the specific `(x', y')`, apply `radial_distortion_value_equivalence`.

**Challenge**: `hden` in this theorem takes `∀ x' y'`, so `hden x' y'` gives OpenCV
denominator nonzero at that specific point. Then `radial_distortion_value_equivalence`
gives `hden_oti`. However, the statement uses inline real expressions (not `sensorRadius`),
so the proof must connect `r_n^2 = x'^2 + y'^2` to `(sensorRadius ⟨x', y'⟩)^2`.

```lean
have h_sq : (sensorRadius ⟨x', y'⟩)^2 = x'^2 + y'^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
```

### Closing move

After all substitutions, both sides are equal expressions in `x', y', fx, cx, p1, p2, R_cv`.
Close with:
```lean
field_simp [hF, hw, hws]
ring
```

or `ring` alone if `field_simp` already cleared denominators.

### Automation budget

- `intro x' y'`
- Multiple `rw [...]` or `simp only [...]` with conversion hypotheses
- `have h_sq` and `have hden_oti` (inline)
- `have h_radial := radial_distortion_value_equivalence ...`
- `field_simp [hF, ...]` + `ring` to close the arithmetic

**Budget limit**: At most 4 manual `rw` steps for the algebraic normalization; if stuck,
isolate the problematic sub-expression in a named `have` rather than continuing to rw blindly.

---

## Theorem 3: opencv_openlensio_full_pipeline_pixel_iff

### Goal shape

```
(∀ x' y', pixel_cv x' y' = pixel_oti x' y') ↔
(l1 = k1/F^2 ∧ l3 = k2/F^4 ∧ l5 = k3/F^6 ∧ l2 = k4/F^2 ∧ l4 = k5/F^4 ∧ l6 = k6/F^6 ∧
 q1 = p1/F^2 ∧ q2 = p2/F^2 ∧ F = (w/ws)*fx ∧ ΔPx = (w/ws)*(cx - ws/2) ∧ ws/w = fx)
```

### Opening move

```lean
constructor
```

Split into ← and → directions.

### ← direction

```lean
· rintro ⟨hl1, hl3, hl5, hl2, hl4, hl6, hq1, hq2, hF_eq, hΔPx, hscale⟩
  exact opencv_openlensio_full_pipeline_pixel_sufficiency ... hl1 ... hscale
```

Direct application of the sufficiency theorem. Trivial once that theorem exists.

### → direction

**Strategy**: extract each condition by specializing `∀ x' y'` at chosen points.

**Step 1: Extract linear projection conditions (F, ΔPx)**

From `pixel_cv x' y' = pixel_oti x' y'` for all x', the x'−linear part must agree.
The pixel expressions are linear in x' (treating R_cv as a function that depends on
x'^2+y'^2). By setting `y' = 0`, `r_n = |x'|`, the y-dependence in tangential vanishes:

At y'=0:
- `pixel_cv = fx*(R_cv(x'^2)*x' + p2*(3*x'^2)) + cx`
- `pixel_oti = (ws/w)*(R_oti(F*|x'|)*F*x' + q2*(3*(F*x')^2) + ΔPx) + ws/2`

The linear-in-x' part: use `principal_point_conversion_iff` or specialize at a point
where R_cv = 1 (e.g. x' = 0 and radial terms vanish). Actually for extraction, the
cleanest approach is:

At `(x'=1, y'=0)` and `(x'=0, y'=0)` (to separate the cx-like constants from x-coefficients).
Use a version of `principal_point_conversion_necessary` adapted for the radial+tangential case.

**Alternative**: Prove this by showing that the linear parts (R_cv*x' terms) force F,
and the constant parts force ΔPx, using polynomial identification. The Vandermonde
specialization approach from `whole_radial_polynomial_iff` applies here.

**Step 2: Extract radial coefficient conditions**

After extracting F and ΔPx, reduce to showing:
```
∀ x' y', fx*(R_cv*x' + tangential_cv) = fx*(R_oti_normalized*x' + tangential_oti)
```
which after dividing by fx (non-zero) and isolating the radial part (specializing y'=0)
gives:
```
∀ x', R_cv(x'^2) = R_oti(F^2*x'^2)
```
Apply `whole_radial_polynomial_iff` (for numerator and denominator separately) to extract
the coefficient conditions.

**Step 3: Extract tangential coefficient conditions**

After radial conditions known, the remaining equality is:
```
∀ x' y', tangential_cv(x', y') = (ws/w) * tangential_oti(F*x', F*y')
```
Apply `whole_tangential_field_iff` for q1 and q2.

**Step 4: Extract ws/w = fx**

After all coefficient conditions known, both sides simplify (by sufficiency reasoning)
to:
```
fx * δx_cv = (ws/w) * δx_cv  for all x', y'
```
where `δx_cv = 2*p1*x'*y' + p2*(x'^2+y'^2+2*x'^2)`.

By `hp : p1 ≠ 0 ∨ p2 ≠ 0`, there exist (x', y') with `δx_cv ≠ 0`.
- If `p2 ≠ 0`: specialize at `(x'=1, y'=0)`, `δx_cv = 3*p2 ≠ 0`; divide to get `fx = ws/w`.
- If `p1 ≠ 0`: specialize at `(x'=1, y'=1)`, `δx_cv = 2*p1 + 3*p2`; with `p2 = 0`, `δx_cv = 2*p1 ≠ 0`.

**Expected difficulty**: High. Step 4 is clean; Steps 1–3 require careful decoupling of
mixed polynomial expressions. The proof may need 1–2 new helper lemmas to isolate the
polynomial identification subgoals.

### Algebra anti-spiral safeguard

If the → direction stalls after 3 tactic attempts at any single subgoal, emit a PROOF STOP
and report the exact goal shape. The likely culprit is the entanglement of R_cv in the
univeral specialization — the radial term depends on r_n which depends on x'^2+y'^2,
making it non-polynomial in x'. **This may require rephrasing the specialization.**

Specifically: specializing at `(x'=t, y'=0)` gives `r_n^2 = t^2`, so `R_cv(t^2)` is a
rational function in `t^2`. To extract polynomial conditions, specialize at `t=1, 2, 3`
(as in `whole_radial_polynomial_iff`) — this is valid if `R_cv(1) = some_known_value`,
which requires the specific denominator nonzero condition at those points. The `hden`
universal hypothesis provides this.

### Helper lemmas (may be needed)

1. `cv_pixel_eq_linear_iff` — extract F, ΔPx from pixel agreement (if the principal-point
   approach doesn't directly apply to the full nonlinear expression)
2. Possibly: a lemma connecting `pixel_cv x' 0 = pixel_oti x' 0` (reduced case) to the
   coefficient conditions — may reduce the complexity by separating radial from tangential

### Automation budget

- `constructor` for iff split
- ← direction: single `exact` applying sufficiency
- → direction: `intro h`; multiple `have` statements specializing `h` at chosen points;
  `field_simp` + `nlinarith` for the coefficient extraction steps;
  `rcases hp with hp1 | hp2` for the tangential case split
- Max 3 manual rw steps per algebraic sub-goal; isolate to `have` otherwise

---

## Key Lean facts to import/apply

| Fact | Source |
|------|--------|
| `radial_distortion_value_equivalence` | `PixelEquivalence.lean` |
| `whole_radial_polynomial_iff` | `DistortionConversion.lean` |
| `whole_tangential_field_iff` | `DistortionConversion.lean` |
| `principal_point_conversion_iff` | `PrincipalPointConversion.lean` |
| `Real.sq_sqrt` | Mathlib |
| `Real.sqrt_mul`, `Real.sqrt_sq` | Mathlib |
| `pow_ne_zero` | Mathlib |
| `field_simp`, `ring`, `nlinarith` | Mathlib tactics |
