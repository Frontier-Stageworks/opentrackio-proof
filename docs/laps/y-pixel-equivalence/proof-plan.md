---
name: y-pixel-equivalence-proof-plan
description: Proof plan for the y-axis mirror of the full pipeline pixel-equivalence theorems, derived from direct reading of the actual x-axis proof scripts (not the stale Vandermonde sketch in the sibling slice's own proof-plan.md, which predates the simpler helper-lemma approach the x-proof actually ended up using)
metadata:
  type: project
---

# Proof Plan — Y-Pixel Pipeline Equivalence

**Grounding note:** the sibling slice's `proof-plan.md` (x-axis) describes an earlier, more complex Vandermonde-based extraction strategy for the → direction of the iff theorem. The *actual* realized `Pipeline/PixelIff.lean` + `Pipeline/PixelIffHelpers.lean` took a simpler path: the → direction derives only `ws/w = fx` (not a full reconstruction of every coefficient from scratch — those are still hypotheses), via two short helper lemmas (`pixel_eq_implies_tangential_gap`, `tangential_gap_forces_scale`) using direct point-specialization, not Vandermonde. This plan mirrors the **actual, realized** x-proof, confirmed by reading `Pipeline/PixelSufficiency.lean`, `Pipeline/PixelIff.lean`, and `Pipeline/PixelIffHelpers.lean` in full before writing this plan.

## Axis-invariant fact (confirmed, not assumed)

The radial numerator/denominator equality sub-proofs in the x-theorem (`h_num`, `h_den` local `have`s in `PixelSufficiency.lean:72-89`) depend only on `x'^2+y'^2`, `hl1..hl6`, and `F`. They are **literally unchanged** under the y-mirror — `x'^2+y'^2 = y'^2+x'^2` by commutativity, and the hypotheses `hl1..hl6` don't reference `x'`/`y'` at all. These two `have`s will be copied verbatim (same statement, same proof) into the y-files, not algebraically re-derived.

## Theorem 1: `opencv_openlensio_full_pipeline_pixel_sufficiency_y`

### Goal shape

Same shape as the x-theorem with `x' ↦ y'` in the "primary" position and the tangential term swapped to the y-shape (`p1*(x'²+y'²+2y'²) + 2*p2*x'y'`, per `whole_tangential_field_2d_iff`'s δy component), and all linear-projection parameters renamed `fx→fy, cx→cy, w→h, ws→h_shader, ΔPx→ΔPy`.

### Opening move

```lean
intro x' y'
have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
have hF4 : F ^ 4 ≠ 0 := pow_ne_zero _ hF
have hF6 : F ^ 6 ≠ 0 := pow_ne_zero _ hF
have hden_xy := hden x' y'
have hhs_eq : h_shader = h * fy := by
  have h := (div_eq_iff hh).mp hscale
  rw [mul_comm] at h; exact h
have hfy : fy ≠ 0 := by rw [← hscale]; exact div_ne_zero hhs hh
```

(Direct rename of the x-proof's `hws_eq`/`hfx` block — no algebraic content differs.)

### Core algebraic computation

```lean
have h_num : <verbatim copy of PixelSufficiency.lean's h_num, unchanged> := by
  have hFsq : (F * x') ^ 2 + (F * y') ^ 2 = F ^ 2 * (x' ^ 2 + y' ^ 2) := by ring
  rw [hFsq, hl1, hl3, hl5]; field_simp [hF2, hF4, hF6]
have h_den : <verbatim copy, unchanged> := by
  have hFsq : (F * x') ^ 2 + (F * y') ^ 2 = F ^ 2 * (x' ^ 2 + y' ^ 2) := by ring
  rw [hFsq, hl2, hl4, hl6]; field_simp [hF2, hF4, hF6]
rw [h_num, h_den, hq1, hq2, hΔPy, hF_eq, hhs_eq]
field_simp [hh, hfy, hden_xy]
ring
```

### Hard step

None beyond what the x-proof already discharged — `h_num`/`h_den` are identical, and the final `field_simp; ring` is expected to close the same way since the tangential-term algebra (`q1=(p1/F²)`, `q2=(p2/F²)` substituted into `q1*((Fx)²+(Fy)²+2(Fy)²) + 2*q2*(Fx)(Fy)`) reduces to `p1*(x²+y²+2y²) + 2*p2*xy` by the same field-arithmetic shape as the x-case's `q1,q2` substitution — confirmed by hand-expansion before writing Lean, not assumed:
```
q1*(F²x'²+F²y'²+2F²y'²) + 2*q2*F²x'y' = (p1/F²)*F²*(x'²+y'²+2y'²) + 2*(p2/F²)*F²*x'y' = p1*(x'²+y'²+2y'²) + 2*p2*x'y'
```

### Automation budget

Identical to the x-theorem's budget (0 manual algebra-tripwire-relevant steps expected; `field_simp` + `ring` closes, same as x).

---

## Helper lemmas (`PixelIffHelpersY.lean`, namespace `PipelineEquivalence`)

### `radial_ratio_scaled_eq` — reuse decision

**Decision: do NOT reuse the existing lemma with swapped arguments.** Calling it as `radial_ratio_scaled_eq ... F y' x' ... hden_yx` would require `hden_yx : 1+k4*(y'²+x'²)+... ≠ 0`, syntactically different from the available `hden_xy : 1+k4*(x'²+y'²)+... ≠ 0` (propositionally equal via `add_comm`, not definitionally). Rather than threading an extra rewrite through every call site, the y-helpers re-derive the needed radial fact locally via the same `h_num`/`h_den` pattern as Theorem 1 — this keeps the helper file self-contained and avoids a fragile cross-file argument-order dependency. (If this turns out to need more than 2 manual `rw` steps to wire up, treat as an ALGEBRA STOP trigger per the gate, not a reason to force the reuse.)

### `tangential_scaled_eq_y`

```lean
lemma tangential_scaled_eq_y
    (p1 p2 q1 q2 F x y : ℝ)
    (hF : F ≠ 0)
    (hq1 : q1 = p1 / F ^ 2) (hq2 : q2 = p2 / F ^ 2) :
    q1 * ((F*x)^2 + (F*y)^2 + 2*(F*y)^2) + 2 * q2 * (F*x) * (F*y)
    = p1 * (x^2 + y^2 + 2*y^2) + 2 * p2 * x * y := by
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero _ hF
  rw [hq1, hq2]; field_simp [hF2]
```

Direct mirror of `tangential_scaled_eq` (swap which coefficient multiplies the squared term vs. the cross term, per the confirmed axis-swap correspondence in `proof-capsule.md`).

### `principal_offset_cancels_y`

```lean
lemma principal_offset_cancels_y
    (cy h_shader h ΔPy : ℝ)
    (hh : h ≠ 0) (hhs : h_shader ≠ 0)
    (hΔPy : ΔPy = (h / h_shader) * (cy - h_shader / 2)) :
    (h_shader / h) * ΔPy + h_shader / 2 = cy := by
  rw [hΔPy]; field_simp [hh, hhs]; ring
```

Verbatim rename of `principal_offset_cancels` — no algebraic content differs.

### `tangential_gap_forces_scale_y`

Specialization points **recomputed directly from the new term shape**, not copied blindly from the x-version's points (verified by hand before writing, in `proof-capsule.md`'s derivation):

```lean
lemma tangential_gap_forces_scale_y
    (p1 p2 fy h_shader h : ℝ)
    (hh : h ≠ 0) (hhs : h_shader ≠ 0)
    (hp : p1 ≠ 0 ∨ p2 ≠ 0)
    (hgap : ∀ x y : ℝ,
        (fy - h_shader / h) * (p1 * (x^2 + y^2 + 2*y^2) + 2 * p2 * x * y) = 0) :
    h_shader / h = fy := by
  rcases hp with hp1 | hp2
  · -- p1 ≠ 0: (1,0) directly isolates p1 — term = p1*(1+0+0) = p1
    have h10 := hgap 1 0
    simp only [mul_zero, zero_mul, add_zero] at h10
    -- h10 : (fy - h_shader/h) * p1 = 0  (after simplifying x=1,y=0)
    rcases mul_eq_zero.mp h10 with hc | hp1z
    · linarith
    · exact absurd hp1z hp1
  · -- p2 ≠ 0: (1,1) and (1,-1) subtract to isolate p2 — see proof-capsule.md derivation
    have h11  := hgap 1 1
    have h1m1 := hgap 1 (-1)
    have : (fy - h_shader / h) * (4 * p2) = 0 := by linarith
    rcases mul_eq_zero.mp this with hc | hp2z
    · linarith
    · have : p2 = 0 := by linarith
      exact absurd this hp2
```

**Anticipated wrinkle:** `hgap 1 0` after substitution gives `(fy - h_shader/h) * (p1*(1+0+0) + 2*p2*1*0) = 0`; the `simp only [mul_zero, zero_mul, add_zero]` call is expected to reduce `p1*(1+0+0)` — note `1^2+0^2+2*0^2` needs `one_pow`/`zero_pow`/numeral simplification, not just `mul_zero`/`zero_mul`. **Revise to `norm_num` or `ring_nf` if the listed `simp only` lemma set doesn't fully close the numeral arithmetic** — flag this as the single most likely spot for a first-attempt failure, to be resolved via the standard failure-recording protocol if it occurs, not guessed around in advance.

### `pixel_eq_implies_tangential_gap_y`

Mirrors `pixel_eq_implies_tangential_gap` exactly in structure: specialize `h` (the universal y-pixel-equality hypothesis) at `(x', y')`, establish the radial-ratio fact (via the local `h_num`/`h_den`-style derivation, per the reuse decision above — **not** via calling the x-file's `radial_ratio_scaled_eq`), the two tangential-term facts via `tangential_scaled_eq_y`, the offset fact via `principal_offset_cancels_y`, the scale fact `h_shader/h*F=fy` (mirrors `h_scale` verbatim), then close via `linear_combination` mirroring the x-version's combination exactly (same coefficient structure, `x'↦y'`, `p1↦p2` roles already baked into the lemma statements above).

---

## Theorem 2: `opencv_openlensio_full_pipeline_pixel_iff_y`

Direct mirror of `PixelIff.lean`'s `constructor` / two-direction structure:
- ← direction: `exact opencv_openlensio_full_pipeline_pixel_sufficiency_y ...`
- → direction: `exact tangential_gap_forces_scale_y ... (pixel_eq_implies_tangential_gap_y ...)`

No new algebraic content beyond what Theorem 1 and the helpers already establish — this theorem is expected to be a near-mechanical composition, same as the x-version.

## Required discrimination check (y-axis mutation-test analogs)

Per the MAPS handoff, at least 2 analogs of `MutationTests.lean`'s existing q1/q2-power-degeneracy and coefficient-swap theorems, restated for the y-shape:

1. **Wrong F-power for y-side tangential coefficient:** mirror `wrong_q1_power_F4_forces_power_degeneracy` — if the y-consistency condition used `q1 = p1/F^4` (wrong power) instead of `p1/F^2`, show this forces a degenerate condition on `F` (same proof shape as the existing theorem, swap which variable plays which role per the confirmed correspondence).
2. **Coefficient-swap variant:** mirror the existing `l1↔k2`-style swap theorems, but for the y-tangential pairing (p1 pairs with the squared-term coefficient on the OTI side, not the cross-term one) — show pairing a y-side coefficient with the wrong partner forces an almost-always-false arithmetic coincidence, same as the existing swap theorems.

File location: new theorems added to a new `Pipeline/MutationTestsY.lean`, or appended to the existing `MutationTests.lean` if its import structure already supports the y-shape terms without new imports (confirm in proof-run-log.md before choosing).

## Automation budget / tripwires

Same limits as the project-wide gate: 2 failed algebra attempts on the same goal → `ALGEBRA STOP`; 2 manual `rw` steps for rearrangement → stop and use a solver or `ALGEBRA STOP`; `field_simp` denominators/nonzero list stated before each call.

## Key Lean facts to import/apply

| Fact | Source |
|------|--------|
| `whole_tangential_field_2d_iff` (confirms y-term shape) | `DistortionConversion.lean:201` |
| `pow_ne_zero` | Mathlib |
| `field_simp`, `ring`, `linarith`, `mul_eq_zero`, `linear_combination` | Mathlib tactics |

## Reusable technique check

```
REUSABLE TECHNIQUE CHECK:
- Technique name: Mechanical axis-mirroring via confirmed variable/coefficient substitution
- Applicability conditions: a proof over OpenCV/OpenLensIO pixel pipelines where the x and y
  axes are mathematically symmetric except for which tangential coefficient plays which role
- Lean approach: re-derive axis-invariant local `have`s verbatim; re-specialize helper lemmas'
  point choices by hand-deriving from the swapped term shape (never blindly swap specialization
  points without recomputing); keep new files self-contained rather than reusing x-file lemmas
  with argument-order tricks that would need extra rewriting
- Recorded in proof-plan.md: yes
- Recorded in proof-review.md: pending (after proof completes)
```
