---
name: opencv-openlensio-pipeline-equivalence-proof-plan-pe04b
description: Proof plan for SLICE-PE-04b — forward direction of opencv_openlensio_full_pipeline_pixel_iff
metadata:
  type: project
---

# Proof Plan — PE-04b: Forward Direction of pixel_iff

## Goal shape

The → direction receives:

```
h : ∀ x' y', CV_pixel_x x' y' = OTI_pixel_x x' y'
⊢ ws / w = fx
```

Classification: **implication** (intro h, then equality goal).

The route:
```
h : universal pixel equality
  → pixel_eq_implies_tangential_gap (new lemma)
  → tangential_gap_forces_scale (already compiled)
  → ws / w = fx
```

## Opening move

```lean
intro h
exact PipelineEquivalence.tangential_gap_forces_scale p1 p2 fx ws w hw hws hp
  (PipelineEquivalence.pixel_eq_implies_tangential_gap ... h)
```

`tangential_gap_forces_scale` is already proved in `PixelIffHelpers.lean`.
`pixel_eq_implies_tangential_gap` is the new lemma to add.

## New lemma: pixel_eq_implies_tangential_gap

**Statement**: Given all conversion hypotheses and `h : ∀ x' y', CV = OTI`,

```lean
∀ x' y' : ℝ,
  (fx - ws / w) * (2 * p1 * x' * y' + p2 * (x' ^ 2 + y' ^ 2 + 2 * x' ^ 2)) = 0
```

This is the output type required by `tangential_gap_forces_scale`.

**File**: `PixelIffHelpers.lean`, inside `namespace PipelineEquivalence`.

### Proof of pixel_eq_implies_tangential_gap

Opening move: `intro x' y'`, then `have hspec := h x' y'`.

**Step 1 — Instantiate three helper lemmas**:

```lean
have hden_xy := hden x' y'
have h_rad := radial_ratio_scaled_eq k1 k2 k3 k4 k5 k6 l1 l2 l3 l4 l5 l6 F x' y'
              hF hl1 hl3 hl5 hl2 hl4 hl6 hden_xy
have h_tang := tangential_scaled_eq p1 p2 q1 q2 F x' y' hF hq1 hq2
have h_offset := principal_offset_cancels cx ws w ΔPx hw hws hΔPx
```

**Step 2 — Derive ws/w * F = fx**:

```lean
have h_scale : ws / w * F = fx := by rw [hF_eq]; field_simp [hws]
```

Justification: `hF_eq : F = (w/ws)*fx`. Substituting: `ws/w * ((w/ws)*fx) = fx`. 
After `field_simp [hws]` clears `ws` from the denominator, `ring` or the field_simp 
normal form closes it.

**Step 3 — Rewrite hspec using h_rad and h_tang**:

```lean
rw [h_rad, h_tang] at hspec
```

After this rewrite, `hspec` has the form:
```
fx * (R * x' + T) + cx = (ws/w) * (R * x' * F + T + ΔPx) + ws/2
```
where:
- `R = (1+k1*(x'^2+y'^2)+k2*(x'^2+y'^2)^2+k3*(x'^2+y'^2)^3) /
       (1+k4*(x'^2+y'^2)+k5*(x'^2+y'^2)^2+k6*(x'^2+y'^2)^3)`
- `T = 2*p1*x'*y' + p2*(x'^2+y'^2+2*x'^2)`

**Step 4 — Close by linear_combination**:

```lean
linear_combination hspec +
  ((1 + k1*(x'^2+y'^2) + k2*(x'^2+y'^2)^2 + k3*(x'^2+y'^2)^3) /
   (1 + k4*(x'^2+y'^2) + k5*(x'^2+y'^2)^2 + k6*(x'^2+y'^2)^3) * x') * h_scale +
  h_offset
```

**Why this closes the goal**: The residual check by `ring` verifies:

```
(fx - ws/w) * T
  - [(fx*(R+T)+cx - (ws/w)*(R*F+T+ΔPx) - ws/2)  -- hspec diff
     + R * (ws/w*F - fx)                           -- R * h_scale diff
     + (ws/w*ΔPx + ws/2 - cx)]                    -- h_offset diff
= 0
```

Expanding: all R-terms cancel (`ws/w*R*F - fx*R + ws/w*R*F*(-1) + fx*R = 0`),
all constant terms cancel, leaving `(fx-ws/w)*T - (fx-ws/w)*T = 0`. ✓

The residual is a polynomial identity in R and T. Since R involves division,
`ring` handles it in the field ℝ.

## Expected hard step

The `rw [h_rad, h_tang] at hspec` step: these are syntactic rewrites against
the exact form of `hspec`. The terms in `hspec` are instantiated at the same
`(x', y')` as h_rad and h_tang, so the match should be exact.

If the rewrite fails (syntactic mismatch), the fallback is to embed `h_rad` and
`h_tang` directly into the `linear_combination` expression without the `rw` step.

## Automation budget

| Step | Tactic | Justification |
|---|---|---|
| h_scale derivation | `field_simp [hws]` | Clear ws from denominator — bounded, single use |
| Step 3 | `rw [h_rad, h_tang]` | Syntactic rewrites — no search |
| Step 4 | `linear_combination` | High-level algebra closer — appropriate, hard step explicit |
| Residual | `ring` | Polynomial identity check — residual of linear_combination |

NOT allowed:
- `nlinarith` on full pixel equality
- `field_simp` on the full hspec
- `ring_nf` on the full hspec
- Any expansion of the k1..k6 polynomial in the main theorem

## Composition: forward direction in PixelIff.lean

After `pixel_eq_implies_tangential_gap` is in PixelIffHelpers.lean:

```lean
· -- → direction
  intro h
  exact PipelineEquivalence.tangential_gap_forces_scale p1 p2 fx ws w hw hws hp
    (PipelineEquivalence.pixel_eq_implies_tangential_gap
      k1 k2 k3 k4 k5 k6 p1 p2 l1 l2 l3 l4 l5 l6 q1 q2
      fx cx ws w F ΔPx
      hw hws hF hl1 hl3 hl5 hl2 hl4 hl6 hq1 hq2 hF_eq hΔPx hden h)
```

## Stop rule

Stop and emit PROOF STOP if:
- `rw [h_rad]` fails with a mismatch error
- `linear_combination` fails with a ring residual that is not 0
- Any tactic path repeats
