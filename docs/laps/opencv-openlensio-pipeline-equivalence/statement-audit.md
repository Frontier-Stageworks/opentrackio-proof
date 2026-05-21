---
name: opencv-openlensio-pipeline-equivalence-statement-audit
description: Statement audit for the three pipeline equivalence theorems — checks alignment between formal statements and intended claims
metadata:
  type: project
---

# Statement Audit — OpenCV/OpenLensIO Full Pipeline Equivalence

## Audit scope

This audit covers:
1. `undistortOpenCV` definition shape
2. `opencv_openlensio_radial_pipeline_eq` statement
3. `opencv_openlensio_full_pipeline_pixel_sufficiency` statement
4. `opencv_openlensio_full_pipeline_pixel_iff` statement

---

## 1. undistortOpenCV definition

### Intended domain concept

OpenCV's Brown-Conrady distortion model applied to normalised coordinates.
Given a normalised distorted input point `ε' = (x', y')`:
- `r = sqrt(x'^2 + y'^2)` (normalised radius — NOT screen-space radius)
- `R_cv = (1 + k1·r^2 + k2·r^4 + k3·r^6) / (1 + k4·r^2 + k5·r^4 + k6·r^6)`
- `δx = 2·p1·x'·y' + p2·(r^2 + 2·x'^2)` (tangential — uses normalised r, not F·r)
- Output: `R_cv·x' + δx`

### Formal shape

```lean
noncomputable def undistortXCV
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (ε : SensorPoint)
    (hden : 1 + k4*(sensorRadius ε)^2 + k5*(sensorRadius ε)^4 + k6*(sensorRadius ε)^6 ≠ 0) : ℝ :=
  let r := sensorRadius ε
  ((1 + k1*r^2 + k2*r^4 + k3*r^6) / (1 + k4*r^2 + k5*r^4 + k6*r^6)) * ε.x
  + 2*p1*ε.x*ε.y + p2*(r^2 + 2*ε.x^2)
```

### Alignment check

- **Uses `sensorRadius`** — same as OTI, so `r = sqrt(ε.x^2 + ε.y^2)`. ✓
- **k1,k2,k3=numerator; k4,k5,k6=denominator** — matches DistortionConversion.lean. ✓
- **Tangential uses `r^2 = sensorRadius^2`** — consistent with OpenCV formula. ✓
- **Does NOT use `RadialCoefficients`** — avoids naming-convention conflict. ✓
- **`hden` predicate is at the specific normalised radius** — mirrors `denominatorNonzero`. ✓

### Potential issues

- `sensorRadius ε = sqrt(...)` requires `Real.sq_sqrt` in proofs to get `(sensorRadius ε)^2 = ε.x^2 + ε.y^2`. Flag for proof plan.
- The `let r` binding uses `sensorRadius ε`, so `r^2 ≠ ε.x^2 + ε.y^2` definitionally — proof by `Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))`.

---

## 2. opencv_openlensio_radial_pipeline_eq

### Intended claim

After parameter conversion, the OpenCV radial scale factor at normalised radius `r_n`
equals the OTI radial scale factor at screen radius `r_s = F·r_n`, and consequently
`undistortPointCV` (with zero tangential) equals `(1/F)` times `undistortPoint` (with zero
tangential) applied to the scaled screen point `⟨F·ε'.x, F·ε'.y⟩`.

### Proposed statement

```lean
theorem opencv_openlensio_radial_pipeline_eq
    (k1 k2 k3 k4 k5 k6 : ℝ)
    (l1 l3 l5 l2 l4 l6 : ℝ)
    (F : ℝ) (hF : F ≠ 0) (hF_pos : 0 < F)
    (ε' : SensorPoint)
    (hl1 : l1 = k1/F^2) (hl3 : l3 = k2/F^4) (hl5 : l5 = k3/F^6)
    (hl2 : l2 = k4/F^2) (hl4 : l4 = k5/F^4) (hl6 : l6 = k6/F^6)
    (hden_cv : 1 + k4*(sensorRadius ε')^2 + k5*(sensorRadius ε')^4
                 + k6*(sensorRadius ε')^6 ≠ 0) :
    -- The x-component of OpenCV undistortion (no tangential) equals
    -- (1/F) × OTI undistortX (no tangential) at the screen point F·ε'
    let k_oti : RadialCoefficients := ⟨l1, l2, l3, l4, l5, l6⟩
    let ε_screen : SensorPoint := ⟨F * ε'.x, F * ε'.y⟩
    let hden_oti : denominatorNonzero k_oti (sensorRadius ε_screen) := ...
    undistortXCV k1 k2 k3 k4 k5 k6 0 0 ε' hden_cv =
    (1/F) * undistortX k_oti TangentialCoefficients.zero ε_screen hden_oti
```

### Alignment check

- **Statement matches intent**: the radial-only OTI output (in screen space) is exactly
  `F` times the radial-only OpenCV output (in normalised space). ✓
- **Relies on `radial_distortion_value_equivalence`** for the equality of R_cv and R_oti. ✓
- **`hF_pos` needed** to derive `sensorRadius ⟨F·x, F·y⟩ = F · sensorRadius ε'`
  (requires `|F| = F` i.e., F > 0). This is not derivable from `hF : F ≠ 0` alone. Flag.
- **`hden_oti` construction**: needs to be built from `hden_cv` + conversion theorems
  + `radial_distortion_value_equivalence`. Not a trivial construction; see proof plan.

### Potential issues

- `sensorRadius ⟨F*ε'.x, F*ε'.y⟩ = F * sensorRadius ε'` requires `F > 0`. ✓ (hF_pos covers it)
- The theorem statement uses `let` inside the statement, which in Lean 4 creates local
  `have`-style bindings. Consider whether to spell these out as hypotheses instead.

---

## 3. opencv_openlensio_full_pipeline_pixel_sufficiency

### Intended claim

Given all parameter conversions AND `ws/w = fx`, the full pixel-level outputs agree.

### Alignment with computation

Inline computation (after substituting all conversions and `ws/w = fx`):
- OTI pixel: `fx·R_cv·x' + (ws/w)·δx_cv + cx = fx·R_cv·x' + fx·δx_cv + cx`
- CV pixel:  `fx·R_cv·x' + fx·δx_cv + cx`
- These are identical. ✓

The sufficiency theorem is a forward implication only — no hypotheses about tangential
coefficients being nonzero are required.

### Statement shape

```lean
theorem opencv_openlensio_full_pipeline_pixel_sufficiency
    (k1 k2 k3 k4 k5 k6 p1 p2 : ℝ)
    (l1 l3 l5 l2 l4 l6 q1 q2 : ℝ)
    (fx cx ws w F ΔPx : ℝ)
    (hw : w ≠ 0) (hws : ws ≠ 0) (hF : F ≠ 0) (hF_pos : 0 < F)
    (hden : ∀ x' y' : ℝ, <OpenCV denom nonzero at r^2 = x'^2+y'^2>)
    (hl1 : l1 = k1/F^2) ... (hl6 : l6 = k6/F^6)
    (hq1 : q1 = p1/F^2) (hq2 : q2 = p2/F^2)
    (hF_eq : F = (w/ws)*fx) (hΔPx : ΔPx = (w/ws)*(cx - ws/2))
    (hscale : ws/w = fx) :
    ∀ x' y' : ℝ,
        <pixelOutCV x' y' (with hden applied)> = <pixelOutOTI x' y' (with hden_oti)>
```

The pixel output expressions are spelled out inline in the theorem statement (not via
named defs). This mirrors the style of `PrincipalPointConversion.lean`.

---

## 4. opencv_openlensio_full_pipeline_pixel_iff

### Intended claim

The full iff version: pixel agreement for all normalised points ↔ all conversions + scale.

### Critical question: hypotheses for → direction

For the → direction, we need to extract `ws/w = fx` from universal pixel agreement.
The extraction uses: at `(x', y') = (1, 0)`:

```
CV pixel = fx*(R_cv*1 + 3*p2) + cx
OTI pixel = fx*R_cv*1 + (ws/w)*3*p2 + cx
Equality ⟹ fx * 3*p2 = (ws/w) * 3*p2 ⟹ (fx - ws/w) * p2 = 0
```

If `p2 ≠ 0`, then `fx = ws/w`.

Similarly at `(1, 1)` the cross-term `2*p1` appears.

**Conclusion**: The → direction of the iff requires either:
- `p2 ≠ 0` (sufficient, simpler)
- `p1 ≠ 0 ∨ p2 ≠ 0` (necessary and sufficient)

The theorem statement will use `hp : p1 ≠ 0 ∨ p2 ≠ 0` as a hypothesis.

### Statement alignment

The iff form:
```
(∀ x' y', pixel_cv = pixel_oti) ↔ (all_conversions ∧ ws/w = fx)
```
is TRUE given `hp`. Without `hp`, the → direction fails for pure-radial lenses.

The iff is correctly stated: the LHS is a universal equality claim, the RHS is the complete
set of conditions, and `hp` is an honest hypothesis (not a vacuity trick). ✓

### Scope note

The theorem is stated for the x-pixel component only. A 2D version (both x and y) would
be similar and has the same proof structure; it is deferred to avoid scope creep.
The 1D case captures the full mathematical content.

---

## Overall verdict

All three theorem statements are semantically aligned with the intended claims.
The key design decisions are:
1. Use inline ℝ expressions (not named defs) for pixel output computations.
2. Use `hF_pos : 0 < F` wherever `sensorRadius ⟨F·x, F·y⟩ = F · sensorRadius ε'` is needed.
3. Use `hp : p1 ≠ 0 ∨ p2 ≠ 0` in the iff theorem.

See ambiguity-register.md for tracked open questions.
