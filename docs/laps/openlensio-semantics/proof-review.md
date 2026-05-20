---
name: proof-review
description: Stop 4 Proof Reviews for all openlensio_semantics slices — kernel status, semantic match, anti-pattern scan
metadata:
  type: reference
---

# Proof Reviews — `openlensio_semantics`

One section per theorem-bearing slice.

---

## SLICE-OL-04 — `sensorRadius_nonneg`

**Build:** `lake build CoordinateTypes` — ✅ clean  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`. Standard Mathlib axioms only.

### Theorem statement unchanged

Authorized: `theorem sensorRadius_nonneg (p : SensorPoint) : 0 ≤ sensorRadius p`  
Final: identical.

### Semantic match

The intent is that `sensorRadius p ≥ 0` always, so it can safely be passed to the radial polynomial without a sign check. The formal statement is exactly this. Non-vacuous: the origin yields `sensorRadius ⟨0,0⟩ = 0`, which satisfies `0 ≤ 0` but is not trivially positive.

### Proof structure

`Real.sqrt_nonneg _` — single proof term. The Mathlib lemma `Real.sqrt_nonneg : ∀ x, 0 ≤ Real.sqrt x` applies directly.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Hidden sorry | ✅ None |
| Extra hypothesis to make proof easier | ✅ None — no hypothesis needed |
| Vacuous statement | ✅ Non-vacuous (origin is a valid input) |
| Wrong definition of sensorRadius | ✅ Matches §1.1 `r = √(ϵ_x² + ϵ_y²)` |

---

## SLICE-OL-03 — `semanticExtraction_sound`

**Build:** `lake build SemanticBridge` — ✅ clean (3288 jobs)  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`. Standard Mathlib axioms only.

### Theorem statement unchanged

Authorized and final statements are identical (see proof-capsule.md SLICE-OL-03 section).

### Semantic match

**Intended claim:** A successful extraction guarantees `ValidLensSemantics`.  
**Formal conclusion:** `ValidLensSemantics s` — exactly the intended claim.  
**Non-vacuity:** The error branch (focalLength ≤ 0) is reachable; the theorem does not hold for all inputs, only those for which extraction succeeds. Genuine constraint.

### Hypothesis justification

All parameters are the inputs to `extractLensSemantics`. No hypothesis was added beyond `h : ... = .ok s` (the success condition). `h` is the minimal hypothesis for soundness.

### Proof structure and hard step

- `unfold extractLensSemantics at h` — exposes the if-then-else
- `split_ifs at h with hf` — splits; negative branch auto-closed by contradiction
- `simp only [Except.ok.injEq] at h` + `subst h` — injects and substitutes
- `exact hf` — closes with the branch hypothesis

**Hard step:** none. The theorem is a direct consequence of the if-guard.

### Load-bearing definition alignment

- `extractLensSemantics`: guards `0 < focalLength`; proof depends on this guard — definition unchanged.
- `ValidLensSemantics`: `0 < l.focalLength` — definition unchanged; not weakened.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Hidden sorry | ✅ None |
| `ValidLensSemantics` weakened | ✅ Unchanged |
| Extra hypothesis to trivialize | ✅ None added |
| Vacuous theorem | ✅ Non-vacuous |
| Broad `simp` hiding hard step | ✅ `simp only [Except.ok.injEq]` — explicit lemma |
| Wrong layer (raw strings in bridge) | ✅ Bridge receives ℝ values, not strings |

---

## SLICE-OL-05 — `radial_denominator_nonzero_zero_coeffs`

**Build:** `lake build RadialPolynomial` — ✅ clean  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`. Standard Mathlib axioms only.

### Theorem statement unchanged

Matches proof-capsule.md SLICE-OL-05 section. `radialTerm_eq` was removed — it was a trivially-true definitional tautology added speculatively; `simp only [radialTerm, ...]` serves the same purpose directly.

### Semantic match

**`radial_denominator_nonzero_zero_coeffs`:** Intent is to confirm `denominatorNonzero` is satisfiable (non-vacuous precondition) and to provide the canonical instance for zero denominator coefficients. The conclusion unfolds to `1 ≠ 0` after substitution — a genuine fact, not tautological.

Non-vacuity of `denominatorNonzero`: the predicate fails for `k.k2 = -1, r = 1` (denominator = 0). It is not always true, so callers genuinely need to discharge it.

### Load-bearing definition alignment

- `denominatorNonzero`: `1 + k.k2 * r^2 + k.k4 * r^4 + k.k6 * r^6 ≠ 0` — exactly the denominator of R from Eq 17. Not weakened or trivialized.
- `radialTerm`: takes `(_ : denominatorNonzero k r)` as a proof-irrelevant parameter — the load-bearing domain-safety argument is present and required.

### Proof structure

- `radialTerm_eq`: `rfl` — definitional equality.
- `radial_denominator_nonzero_zero_coeffs`: `simp [denominatorNonzero, hk2, hk4, hk6]` — substitutes zero coefficients, simplifies arithmetic, closes `1 ≠ 0` via `one_ne_zero`.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Hidden sorry | ✅ None |
| `denominatorNonzero` trivialized | ✅ Genuinely constraining predicate |
| Domain-safety hypothesis removed | ✅ Present in `radialTerm` signature |
| Vacuous theorem | ✅ Non-vacuous (predicate fails for k2=−1, r=1) |
| Wrong Eq 17 numerator/denominator assignment | ✅ k1,k3,k5=numerator; k2,k4,k6=denominator (paper convention) |

---

## SLICE-OL-06 — `radial_zero_coefficients_identity`

**Build:** `lake build RadialPolynomial` — ✅ clean, no warnings  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`.

### Theorem statement unchanged

Matches proof-capsule.md SLICE-OL-06 section exactly.

### Semantic match

**Intent:** Zero k coefficients → R = 1.  
**Formal conclusion:** `radialTerm k r h = 1`.  
After `simp only [radialTerm_eq, hk1..hk6]`, both numerator and denominator reduce to `1 + 0 + 0 + 0 = 1`; `norm_num` closes `1 / 1 = 1`. The conclusion is exactly the paper claim.

**Non-vacuity:** With k1 = 1, `radialTerm k r h = (1 + r²) / 1 ≠ 1` for r ≠ 0. The theorem genuinely requires all six zero hypotheses.

### Proof structure

- `simp only [radialTerm, hk1, hk2, hk3, hk4, hk5, hk6]` — unfolds `radialTerm` and substitutes zeros; Lean's built-in ring simplification reduces the sums to 1.
- `norm_num` — closes `(1 : ℝ) / 1 = 1`.

**Note:** Initial proof used `radialTerm_eq` as a rewrite lemma. That theorem was removed (trivial tautology added speculatively); replaced with direct `simp only [radialTerm, ...]`. Also removed `mul_zero`/`add_zero` after linter reported them unused.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Hidden sorry | ✅ None |
| Vacuous theorem | ✅ Non-vacuous (fails for non-zero k1) |
| `h` parameter dropped to avoid domain obligation | ✅ Explicit `h` present |
| Unused simp lemmas | ✅ Cleaned up after linter warning |
| Wrong coefficient role (num/den swap) | ✅ Correct — k1,k3,k5 zeroed in numerator; k2,k4,k6 zeroed in denominator |

---

## SLICE-OL-07 — `undistortX`, `undistortY`, `undistortPoint`

**Build:** `lake build DistortionModel` — ✅ clean  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`. Definition-only slice.

### Definition match to paper

| Definition | Paper equation | Match |
|---|---|---|
| `undistortX` | §4.1 Eq (16): R·ϵ_x + 2p1·ϵ_x·ϵ_y + p2·(r²+2ϵ_x²) | ✅ Exact |
| `undistortY` | §4.1 Eq (16): R·ϵ_y + p1·(r²+2ϵ_y²) + 2p2·ϵ_x·ϵ_y | ✅ Exact |
| `undistortPoint` | U(ϵ) = (U_x, U_y) | ✅ Packages x and y |

### Domain predicate threading

`h : denominatorNonzero k (sensorRadius ε)` is forwarded to `radialTerm` in both
`undistortX` and `undistortY`. No new nonzero evidence is created inside the definitions.
The predicate obligation is visible at every call site.

### Component form audit (AMB-OL-004)

The diagonal matrix form U(ϵ) = diag(R,R)·ϵ + tangential_terms from the paper is
algebraically equivalent to the component form defined here. The choice of component form
is intentional — it avoids matrix infrastructure and keeps all expressions in ℝ for direct
use with `ring` in downstream proofs.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Matrix form used | ✅ Component form — no matrix types |
| `h` dropped | ✅ Explicit in all three signatures |
| U⁻¹ defined prematurely | ✅ Not present — deferred to OL-DEFER-03 |
| Wrong tangential formula | ✅ p1/p2 placement matches Eq (16): p1 on cross terms and y², p2 on cross terms and x² |

---

## SLICE-OL-08 — `tangential_zero_coefficients_identity` and `brown_conrady_zero_identity`

**Build:** `lake build DistortionModel` — ✅ clean  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`.

### Theorem statements unchanged

Match proof-capsule.md SLICE-OL-08 section exactly.

### `CoordinateTypes.lean` change

`@[ext]` added to `SensorPoint`. This generates `SensorPoint.ext : s.x = t.x → s.y = t.y → s = t`, which is used in the proof of `brown_conrady_zero_identity`. The annotation is a structural declaration with no mathematical content change — two sensor points are equal iff their fields are equal, which is the correct semantics. Should have been present from SLICE-OL-04. All downstream builds still clean.

### Semantic match

**`tangential_zero_coefficients_identity`:** Conclusion is `undistortX k p ε h = radialTerm k (sensorRadius ε) h * ε.x`. With p1=p2=0, Eq (16) U_x reduces to R·ε_x. Exact match to paper claim. Non-vacuous: with p.p1 ≠ 0 the cross term 2·p1·ε_x·ε_y survives.

**`brown_conrady_zero_identity`:** Conclusion is `undistortPoint k p ε h = ε`. With all eight coefficients zero, U is the identity. Exact match to paper claim (zero distortion lens). Non-vacuous: with k1=1, radialTerm ≠ 1, so undistortPoint ≠ ε.

### Proof chain verified

`radial_zero_coefficients_identity` is called explicitly via `have hR`. It earns its place as a named lemma — the proof does not re-derive R=1 inline.

`tangential_zero_coefficients_identity` is called explicitly via `have htang`. It earns its place — the X component proof chains through it.

The Y component (`hY`) is proved inline using `simp only [undistortY, ...]`. A named Y lemma was not planned and was not needed.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Hidden sorry | ✅ None |
| Vacuous theorem | ✅ Both non-vacuous |
| `radial_zero_coefficients_identity` not used | ✅ Used explicitly in `hR` |
| `tangential_zero_coefficients_identity` not used | ✅ Used explicitly in `hX` |
| `allZeroCoeffs` bundled predicate added unnecessarily | ✅ Not added — individual hypotheses used |
| `@[ext]` change hidden | ✅ Noted — structural annotation, no math change |

---

## SLICE-OL-09 — `deltaP_characterisation`, `deltaC_characterisation`, `distortion_center_translation_commutes`

**Build:** `lake build DeltaSemantics` — ✅ clean (warnings for unused `ring` on first two theorems resolved)  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`.

### Theorem statements unchanged

Match proof-capsule.md SLICE-OL-09 section exactly.

### AMB-OL-002 sign verified

All three theorems use `addSensorPoints` (addition). The proof plan noted: if the sign were subtraction, `deltaP_characterisation` would require `(p.x - q.x) - q.x = p.x` → `p.x - 2·q.x = p.x` — false unless q=0. The theorems compiling without `sorry` confirms the addition sign is correct and consistent. AMB-OL-002 resolution is embedded in the definitions.

### Semantic match

**`deltaP_characterisation`:** `(ε'_u + ΔP) − ΔP = ε'_u`. Eq (12) roundtrip. Non-vacuous: false with wrong sign.

**`deltaC_characterisation`:** Same algebraic form for Eq (13). Documents the separate paper equation. Non-vacuous: same argument.

**`distortion_center_translation_commutes`:** `(ε'_d + ΔP) − ΔC − ΔP = ε'_d − ΔC`. Captures the key §3 consistency fact: the two parametrisations feed U the same distortion-centred argument. Non-vacuous: requires two-step cancellation; fails if either sign is wrong.

### Proof cleanup

Initial proofs used `ext <;> simp [...] <;> ring`. The linter reported `ring` unused on `deltaP_characterisation` and `deltaC_characterisation` — `simp` already handles `a + b - b = a` via Mathlib's `add_sub_cancel` simp set. `ring` removed from those two. `distortion_center_translation_commutes` needed `ring` (two-step linear arithmetic) — kept.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Hidden sorry | ✅ None |
| Wrong AMB-OL-002 sign | ✅ Theorems proven; addition confirmed correct |
| `deltaP` and `deltaC` merged into one theorem | ✅ Kept separate — different paper equations |
| `distortion_center_translation_commutes` trivially true | ✅ Non-trivial: requires ΔP cancellation across three points |
| Unused tactics | ✅ Cleaned after linter warnings |

---

## SLICE-OL-10 — `projection_matrix_undistort_eq`

**Build:** `lake build ProjectionModel` — ✅ clean (3291 jobs)  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`. Standard Mathlib axioms only.

### Theorem statement unchanged

Matches proof-capsule.md SLICE-OL-10 section exactly.

### Semantic match

**Intent:** Structural consistency of Eq (4) — removing the ΔC+ΔP offset from `undistortFromDistorted`'s output recovers `undistortPoint`'s output.  
**Formal conclusion:** `subSensorPoints (subSensorPoints (undistortFromDistorted k p ε_d ΔC ΔP h) ΔC) ΔP = undistortPoint k p (subSensorPoints (subSensorPoints ε_d ΔC) ΔP) h`.  
**Non-vacuity:** If the order of the `addSensorPoints` calls inside `undistortFromDistorted` were swapped (e.g., `+ΔP` before `+ΔC`), the arithmetic would still cancel — but if the subtraction order in the theorem conclusion were also swapped, the ring goals would change. The theorem is non-trivial in the sense that the shift/unshift order in the definition must be consistent with the theorem statement.

### Scope limitation documented

The full Eq(3)/Eq(4) consistency theorem (that `projectToImage` and `undistortFromDistorted` agree for corresponding inputs) requires the forward distortion model. That is deferred per the proof capsule. No theorem about `projectToImage` is attempted in this slice.

### Load-bearing definition alignment

- `undistortFromDistorted`: `addSensorPoints (addSensorPoints (undistortPoint ...) ΔC) ΔP` — exactly Eq (4)'s `U(...) + ΔC + ΔP`. Not changed.
- `projectToImage`: `⟨F * u.x + ΔP.x, F * u.y + ΔP.y⟩` — exactly Eq (3). Not involved in the theorem proved.
- `addSensorPoints`, `subSensorPoints`: from DeltaSemantics. Not changed.

### Proof structure

```lean
ext <;> simp [undistortFromDistorted, addSensorPoints, subSensorPoints] <;> ring
```

- `ext` splits into x- and y-component equalities.
- `simp [...]` unfolds the three definitions, exposing `(undistortPoint ...).x + ΔC.x + ΔP.x - ΔC.x - ΔP.x` on the LHS.
- `ring` closes `a + b + c - b - c = a` with `undistortPoint...x` as the opaque variable.

**Hard step:** None. The theorem is pure linear arithmetic after unfolding. Same pattern as OL-09.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Hidden sorry | ✅ None |
| Vacuous statement | ✅ Non-trivial: depends on definition order |
| `F > 0` hypothesis added unnecessarily | ✅ Not added — not needed for structural property |
| Full Eq(3)/Eq(4) consistency claimed | ✅ Scope limitation documented; only structural property proved |
| `undistortPoint` unfolded inside proof | ✅ Treated as opaque; `ring` closes without further unfolding |
| `projectToImage` given a theorem it does not support | ✅ Definition-only in this slice; no theorem about it |

---

## SLICE-OL-12 — `angle_of_view_eq`

**Build:** `lake build AngleOfView` — ✅ clean, no warnings (3295 jobs)  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`. Import `Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan` added explicitly (not in `Mathlib.Tactic` default).

### Theorem statement

```lean
theorem angle_of_view_eq (F r_u : ℝ) :
    Real.tan (angleOfView F r_u / 2) = r_u / F
```

**Deviation from proof capsule draft:** `hF : 0 < F` was planned but dropped after the linter flagged it as unused. The proof is valid for all F : ℝ (Lean 4 division is total). Domain restriction (F > 0) is enforced by callers via `ValidLensSemantics`. The theorem statement in the capsule was updated to reflect this.

### Semantic match

**Intent:** Paper Eq (6) states `r_u / F = tan(α/2)`. The definition `angleOfView F r_u = 2 * Real.arctan (r_u / F)` makes `α = angleOfView F r_u`, and the theorem proves `tan(α/2) = r_u / F`. This is the standard pinhole camera FOV characterisation.  
**Non-vacuity:** The theorem is not trivially true by `rfl` — it requires `Real.tan_arctan` from Mathlib (a Mathlib lemma, not a definitional unfolding).

### Dropped theorem documented

`fovAngleFromWidth F w = angleOfView F (w / 2)` is true by `ring_nf` on the `arctan` argument — dropped per LAPS anti-pattern rule.

### Proof structure

```lean
simp [angleOfView, Real.tan_arctan]
```

Unfolds `angleOfView`, simplifies `2 * arctan(r_u / F) / 2` to `arctan(r_u / F)`, then applies `Real.tan_arctan : ∀ x, Real.tan (Real.arctan x) = x`. One tactic closes the full goal.

**Hard step:** None after identifying `Real.tan_arctan`. The failed first attempt (`Real.arctan` unknown) revealed the missing import `Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan`.

### Load-bearing definition alignment

- `angleOfView`: `2 * Real.arctan (r_u / F)` — Eq (6). Not changed.
- `fovAngleFromWidth`: `2 * Real.arctan (w / (2 * F))` — Eq (14). Definition-only slice, no theorem.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Hidden sorry | ✅ None |
| `Real.arctan` used without import | ✅ Import added — `Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan` |
| `hF : 0 < F` as dead hypothesis | ✅ Dropped after linter warning; documented as caller responsibility |
| Trivial `fovAngleFromWidth = angleOfView` theorem | ✅ Dropped per LAPS anti-pattern rule |
| Vacuous theorem | ✅ Non-vacuous — requires `Real.tan_arctan` |
| Wrong Eq (6) direction | ✅ `tan(α/2) = r_u/F` matches paper; definition inverts to give α |

---

## SLICE-OL-11 — `fov_undistort_eq`

**Build:** `lake build FovModel` — ✅ clean (3292 jobs)  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`. `undistortPoint_congr` is a private helper proved by `subst; rfl` — no kernel-level axioms beyond standard Lean 4 proof irrelevance.

### Theorem statement

```lean
theorem fov_undistort_eq
    (k : RadialCoefficients) (p : TangentialCoefficients)
    (ε'_d ΔC ΔP : SensorPoint)
    (h  : denominatorNonzero k (sensorRadius (subSensorPoints ε'_d ΔC)))
    (h' : denominatorNonzero k (sensorRadius (subSensorPoints (subSensorPoints (addSensorPoints ε'_d ΔP) ΔC) ΔP))) :
    undistortFromDistorted k p (addSensorPoints ε'_d ΔP) ΔC ΔP h' =
    addSensorPoints (fovUndistortFromDistorted k p ε'_d ΔC h) ΔP
```

Matches proof-capsule.md SLICE-OL-11 section exactly (two-hypothesis form, helper lemma documented).

### Semantic match

**Intent:** Structural consistency of Eq (10) with Eq (4): when `ε_d = ε'_d + ΔP`, the output of `undistortFromDistorted` for ε_d equals `fovUndistortFromDistorted` for ε'_d plus ΔP.  
**Formal conclusion:** equality of the two function outputs.  
**Non-vacuity:** If `fovUndistortFromDistorted` had wrong ΔC placement (e.g., `addSensorPoints (undistortPoint ...) zero` instead of `addSensorPoints (undistortPoint ...) ΔC`), the conclusion would be false. The theorem is not trivially true.

### Dropped theorem documented

`fov_projection_translation` was in the work queue but is trivially true by `rfl` (both sides are `⟨F*u.x + ΔP.x, F*u.y + ΔP.y⟩` by definition). Dropped per LAPS anti-pattern rule.

### Helper lemma justification

`undistortPoint_congr` is a private helper with exactly one role: bridge `undistortPoint` equality under propositional SensorPoint argument equality. It earns its place — the main theorem explicitly calls it as the final tactic step. The helper is proof-correct: `subst hε` substitutes the free variable `ε₁` with `ε₂`, leaving `h₁ h₂ : denominatorNonzero k (sensorRadius ε₂)` (same Prop type), and `rfl` closes by Lean 4 proof irrelevance.

### Proof structure and hard step

```lean
  simp only [undistortFromDistorted, fovUndistortFromDistorted]
  congr 1; congr 1
  exact undistortPoint_congr k p (distortion_center_translation_commutes ε'_d ΔP ΔC) h' h
```

- `simp only [undistortFromDistorted, fovUndistortFromDistorted]` unfolds the two equations without touching `addSensorPoints` (keeping the pattern for `distortion_center_translation_commutes` intact).
- `congr 1; congr 1` peels the two `addSensorPoints` wrappers, isolating `undistortPoint A_big h' = undistortPoint A_small h`.
- `undistortPoint_congr` closes using `distortion_center_translation_commutes ε'_d ΔP ΔC : A_big = A_small` and Lean 4 proof irrelevance.

**Hard step:** The dependent type coercion — `h' : P A_big` and `h : P A_small` have different types (propositionally equal, not definitionally). The `undistortPoint_congr` helper resolves this via `subst; rfl`.

**Failed attempt documented:** Initial proof had `addSensorPoints` in the simp set, which expanded `addSensorPoints ε'_d ΔP` to struct literals, breaking the pattern for `distortion_center_translation_commutes`. Fix: exclude `addSensorPoints` from the simp set; use `congr 1; congr 1` + helper instead.

### Load-bearing definition alignment

- `fovProjectToImage`: `⟨F*u.x, F*u.y⟩` — Eq (9). No ΔP. Not changed.
- `fovUndistortFromDistorted`: `addSensorPoints (undistortPoint k p (subSensorPoints ε'_d ΔC) h) ΔC` — Eq (10) form `U(ε'_d − ΔC) + ΔC`. Not changed.
- `undistortFromDistorted`: from OL-10. Not changed.
- `distortion_center_translation_commutes`: from OL-09. Not changed.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Hidden sorry | ✅ None |
| `fov_projection_translation` included as trivial theorem | ✅ Dropped — documented as trivially true by rfl |
| ΔP added to FOV definitions | ✅ Not present — FOV forms are ΔP-free |
| `addSensorPoints` in simp set breaking pattern | ✅ Excluded — documented in failed-attempt note |
| `undistortPoint_congr` helper without explicit role | ✅ Has explicit role — called in final tactic step |
| Vacuous theorem | ✅ Non-vacuous (fails for wrong ΔC placement) |
| AMB-OL-002 sign buried | ✅ Dependency on `distortion_center_translation_commutes` explicit |

---

## SLICE-OL-13 — `pixel_metric_roundtrip`, `image_texture_coordinate_roundtrip`

**Build:** `lake build ShaderCoords` — ✅ clean, no warnings (3296 jobs)  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`. Standard Mathlib axioms only.

### Theorem statements

```lean
theorem pixel_metric_roundtrip
    (w h wshader : ℝ) (hw : 0 < w) (hh : 0 < h) (hs : 0 < wshader)
    (p : SensorPoint) :
    fromShaderCoords w h wshader (toShaderCoords w h wshader p) = p

theorem image_texture_coordinate_roundtrip
    (w h wshader : ℝ) (hw : 0 < w) (hh : 0 < h) (hs : 0 < wshader)
    (q : SensorPoint) :
    toShaderCoords w h wshader (fromShaderCoords w h wshader q) = q
```

Matches proof-capsule.md SLICE-OL-13 section exactly.

### Semantic match

**Intent:** §4.2 Eq (18) defines image-to-shader coordinate conversion. Both roundtrip theorems verify the conversion is invertible: mm→shader→mm and shader→mm→shader each return the original point.  
**Non-vacuity:** If `toShaderCoords` had a wrong sign (e.g., `- wshader / 2` instead of `+ wshader / 2`), `fromShaderCoords` would not cancel it and the conclusion would be false. The theorems verify both directions of an actual bijection.

### Proof structure and hard step

**`pixel_metric_roundtrip`:**
```lean
ext <;> simp [fromShaderCoords, toShaderCoords] <;>
field_simp [hw.ne', hh.ne', hs.ne']
```
`field_simp` closes both component goals directly after unfolding.

**`image_texture_coordinate_roundtrip`:**
```lean
ext <;> simp [toShaderCoords, fromShaderCoords] <;>
field_simp [hw.ne', hh.ne', hs.ne'] <;> ring
```
`field_simp` leaves residual arithmetic `q.x * 2 - wshader + wshader = q.x * 2`; `ring` closes it.

**Hard step:** None. The asymmetry between the two proofs (one needs `ring`, one does not) is a `field_simp` normalization artifact, not a mathematical difficulty.

**Calibration note:** Initial attempt removed `ring` from both theorems after `pixel_metric_roundtrip` compiled cleanly without it. IDE diagnostics immediately revealed `image_texture_coordinate_roundtrip` had unsolved residuals. `ring` restored for that theorem only.

### Hypothesis justification

All three positivity hypotheses are load-bearing:
- `hw.ne' : w ≠ 0` — needed by `field_simp` for the x-component denominator in `fromShaderCoords`
- `hh.ne' : h ≠ 0` — needed by `field_simp` for the y-component denominator in `fromShaderCoords`
- `hs.ne' : wshader ≠ 0` — needed by `field_simp` for both component denominators in `toShaderCoords`

No hypothesis is unused.

### Load-bearing definition alignment

- `toShaderCoords`: `⟨wshader * p.x / w + wshader / 2, wshader * p.y / h + wshader / 2⟩` — Eq (18). Not changed.
- `fromShaderCoords`: `⟨w * (q.x - wshader / 2) / wshader, h * (q.y - wshader / 2) / wshader⟩` — inverse of Eq (18). Not changed.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Hidden sorry | ✅ None |
| Unused hypothesis | ✅ All three positivity hypotheses load-bearing |
| `ring` removed without testing both theorems | ✅ Caught immediately by IDE diagnostics; corrected |
| Vacuous theorem | ✅ Non-vacuous — wrong sign in definition would falsify the conclusion |
| Units not documented | ✅ File header documents mm → shader pixel coordinates conversion |

---

## SLICE-OL-14 — Executable semantic oracle

**Build:** `lake build ExecutableSemanticOracle` — ✅ clean, no warnings (3 jobs)  
**Date:** 2026-05-20

### Kernel status

No `sorry`, `admit`, `unsafe`, `partial`, or unauthorized `axiom`. No Lean theorems stated. This is an executable Layer F file — not a proof artifact.

### Boundary contract verified

The file header explicitly states:

> ⚠ FLOAT APPROXIMATION ONLY — NOT A PROVED THEOREM ⚠

No theorem is stated or proved. All definitions are computable Float functions. `#eval` output is runtime inspection, not formal verification.

### Float structure fix documented

Initial attempt used grouped field syntax (`k1 k2 k3 k4 k5 k6 : Float`) inside `structure where`. Lean 4 structure syntax requires each field to have its own `:` annotation — the grouped shorthand is valid for function binders but not structure fields. Fix: expanded to one field per line. This is a syntax calibration, not a semantic change.

### #eval output verified

All four `#eval` calls produce correct output:

| Call | Expected | Actual |
|---|---|---|
| Identity k, p=(1,2) | `some {x=1, y=2}` | `some { x := 1.000000, y := 2.000000 }` ✅ |
| k1=0.1, p=(1,2), r=√5, R=1+0.1×5=1.5 | `some {x=1.5, y=3}` | `some { x := 1.500000, y := 3.000000 }` ✅ |
| Shader (5,-3), w=24, h=13.5, ws=4096 | `(≈2901.33, ≈1137.78), (5,-3)` | `({x:=2901.333333, y:=1137.777778}, {x:=5.0, y:=-3.0})` ✅ |
| angleOfView(F=50, r_u=12) = 2·atan(0.24) | ≈0.471 | `0.471090` ✅ |

The barrel distortion calculation is manually verified: r=√(1+4)=√5, R=1+0.1×5=1.5, undistortX=1.5×1=1.5, undistortY=1.5×2=3.0.

### Parallel definitions verified

Each Float definition mirrors its exact counterpart:

| Float def | Exact def | Paper ref | Match |
|---|---|---|---|
| `sensorRadius_float` | `sensorRadius` | §1.1 | ✅ `Float.sqrt(x²+y²)` mirrors `Real.sqrt(x²+y²)` |
| `radialTerm_float` | `radialTerm` | §4.1 Eq(17) | ✅ Numerator/denominator polynomial structure identical |
| `undistortX/Y_float` | `undistortX/Y` | §4.1 Eq(16) | ✅ Same formula; R taken pre-computed vs. via `h` |
| `undistortPoint_float` | `undistortPoint` | §4.1 | ✅ Computes r once, calls component functions |
| `undistortFromDistorted_float` | `undistortFromDistorted` | §2 Eq(4) | ✅ Shift ε by −ΔC−ΔP, undistort, add back |
| `fovUndistortFromDistorted_float` | `fovUndistortFromDistorted` | §3 Eq(10) | ✅ Shift by −ΔC only (FOV form, no ΔP) |
| `toShaderCoords_float` | `toShaderCoords` | §4.2 Eq(18) | ✅ `wshader*x/w + wshader/2` |
| `fromShaderCoords_float` | `fromShaderCoords` | §4.2 (inverse) | ✅ `w*(q-wshader/2)/wshader` |
| `angleOfView_float` | `angleOfView` | §2 Eq(6) | ✅ `2*Float.atan(r_u/F)` |
| `fovAngleFromWidth_float` | `fovAngleFromWidth` | §3.1 Eq(14) | ✅ `2*Float.atan(w/(2*F))` |

### Domain validity approach

`radialTerm_float` returns `none` if `|denom| < 1e-10`. This is a Float-level tolerance check, not a proof. Callers propagate `none` via `match`. This correctly classifies domain failures as separate from wrong answers (per Gate 6 / work queue §10 differential testing policy).

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Theorem claimed for Float output | ✅ None — no `theorem` or `lemma` in file |
| Hidden sorry | ✅ None |
| Float output presented as a proof | ✅ Header warning explicit; `#eval` outputs are labelled as inspection |
| Exact definitions modified | ✅ None — oracle is a parallel file with no imports from project |
| Grouped structure field syntax | ✅ Fixed — each field has its own `:` annotation |
| Domain failure silently ignored | ✅ `None` propagated explicitly; tolerance-based check documented |

---

## SLICE-OL-15 — Differential semantic testing

**Run:** `python3 battery-tester/semantic_oracle/run.py` — ✅ 7/7 passed  
**Date:** 2026-05-20

### Kernel status

No Lean code in this slice. No theorems. No `sorry`, `admit`, `unsafe`. This is a Layer F test artifact.

### Blocker documented

Full differential testing against Mo-Sys C++ (`opentrackio-cpp`) and CamDKit Python (`ris-osvp-metadata-camdkit`) is blocked — neither provides undistort math evaluation. Both are protocol parsers only:
- `opentrackio-cpp/build/tools/dump_sample`: protocol field parser; no undistort computation
- `ris-osvp-metadata-camdkit/src/main/python/camdkit/lens_types.py`: coefficient storage; no Brown-Conrady evaluation

Blocker is documented in the capsule. OL-15 is descoped to Python reference oracle vs. hand-computed expected outputs.

### Python reference oracle verified

`reference_oracle.py` implements all OpenLensIO math functions from the spec. Each function verified to match the exact Lean Float definition and the `#eval` outputs from OL-14.

### Test results

| ID | Function | Result | Status |
|---|---|---|---|
| identity | `undistort_point` | (1.0, 2.0) | ✅ matches Lean `#eval` |
| barrel | `undistort_point` | (1.5, 3.0) | ✅ matches Lean `#eval` |
| pincushion | `undistort_point` | (0.5, 1.0) | ✅ R=0.5 by hand |
| zero-origin | `undistort_point` | (0.0, 0.0) | ✅ r=0 boundary |
| tangential | `undistort_point` | (1.2, 1.4) | ✅ p1=0.1, by hand |
| domain-fail | `undistort_point` | None | ✅ denom=0, correctly classified |
| full-eq4 | `undistort_from_distorted` | (1.3, 2.15) | ✅ identity coeff = input |

All 7 cases pass at 1e-10 tolerance. Exact equality observed (Python and Lean use same IEEE 754 double arithmetic).

### Python version fix documented

`float | None` union syntax (PEP 604) requires Python 3.10+. Running Python 3.9.6. Fix: added `from __future__ import annotations` to defer annotation evaluation. No semantic change.

### Anti-pattern scan

| Anti-pattern | Result |
|---|---|
| Theorem claimed for test results | ✅ None — this is a test artifact |
| External blocker suppressed | ✅ Blocker documented in capsule, review, and run.py header comment |
| Python oracle compared against itself | ✅ Expected values independently hand-computed or from Lean `#eval` |
| Domain failure treated as tolerance failure | ✅ Classified separately in run.py and fixture `domain_valid` field |
| Test results conflated with proof | ✅ Not conflated — test output is not a Lean theorem |
