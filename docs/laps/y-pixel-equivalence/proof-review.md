---
name: y-pixel-equivalence-proof-review
description: LAPS proof review for the y-pixel pipeline equivalence slice (PROP-003 y-dimension, EVID-006)
metadata:
  type: project
---

# Proof Review — Y-Pixel Pipeline Equivalence

## Kernel Status

`lake build` (full project) — 3316 jobs, build completed successfully. No `sorry`, no `admit`, no unauthorized `axiom` introduced. Exit code 0. Warnings only (unused variables, same categories as the pre-existing x-axis files — see below).

## Forbidden Constructs

- `sorry`: absent (grep-confirmed across all 4 new files)
- `admit`: absent
- unauthorized `axiom`: absent
- `unsafe` / `partial`: absent
- heartbeat limit changes: none
- sorry-warning suppression (`set_option ... sorry false` or similar): none
- `field_simp`/`ring_nf` on the full pixel equation: none (applied only to small helper goals, same discipline as the x-file)

## Statement Unchanged

`opencv_openlensio_full_pipeline_pixel_sufficiency_y` and `opencv_openlensio_full_pipeline_pixel_iff_y`: identical to the frozen form in `proof-capsule.md`. No statement was weakened, no hypothesis was added beyond what the capsule specified, no hypothesis was silently dropped.

## Load-Bearing Definition / Lemma Alignment

| Lemma | File | Role | Status |
|---|---|---|---|
| `radial_ratio_scaled_eq_y` | `PixelIffHelpersY.lean` | OTI radial at (F·x,F·y)·(F·y) = CV radial at (x,y)·y·F | As planned |
| `tangential_scaled_eq_y_sq` | `PixelIffHelpersY.lean` | OTI squared-term tangential half = CV squared-term half | As planned (split from the capsule's single combined lemma — see Hard Step below) |
| `tangential_scaled_eq_y_cross` | `PixelIffHelpersY.lean` | OTI cross-term tangential half = CV cross-term half | As planned (split, same reason) |
| `principal_offset_cancels_y` | `PixelIffHelpersY.lean` | (h_shader/h)·ΔPy + h_shader/2 = cy | As planned, verbatim rename of x-version |
| `tangential_gap_forces_scale_y` | `PixelIffHelpersY.lean` | (fy−h_shader/h)·T_y=0 for all x,y + p nonzero → h_shader/h=fy | As planned, specialization points re-derived (not copied) for the y-term shape |
| `pixel_eq_implies_tangential_gap_y` | `PixelIffHelpersY.lean` | Universal y-pixel equality → tangential gap | As planned |
| `whole_tangential_field_iff_y` | `MutationTestsY.lean` | Local extraction lemma for the discrimination theorems | New, not in original capsule — added when the mutation-test requirement needed its own coefficient-extraction step, analogous to how `MutationTests.lean` itself depends on `whole_tangential_field_iff` |

No existing file (x-axis or otherwise) was modified. All new content lives in 4 new files plus 1 new `lakefile.toml` lib entry (`MutationTestsY`).

## Semantic Match to Intent

The theorem states: given all parameter conversions (same `l_i = k_i/F^(2n)`, `q_i = p_i/F²` as the x-case — the paper's as-published formula, not the corrected alternative, per the handoff's explicit instruction) and `p1≠0∨p2≠0`, the pixel **y**-outputs agree for every normalised input iff `h_shader/h = fy`.

Verified against `docs/laps/y-pixel-equivalence/proof-capsule.md`'s axis-swap correspondence derivation: the y-tangential term `p1*(x'²+y'²+2y'²) + 2*p2*x'*y'` matches `whole_tangential_field_2d_iff`'s δy component (`DistortionConversion.lean:210`) exactly — confirmed by direct inspection before any proof code was written, not assumed.

## Hypothesis Justification

`hp : p1 ≠ 0 ∨ p2 ≠ 0` — same role as the x-theorem: without at least one nonzero tangential coefficient, the y-tangential term is identically zero and universal pixel equality holds trivially without implying `h_shader/h = fy`. Load-bearing and non-vacuous, unchanged from the x-case's justification.

## Hard Step Identified

Same hard step class as the x-slice's own documented hard step (`proof-review-pe04b.md § Hard Step Identified`), hit independently in this session before that precedent was consulted: `rw [h_tang] at hspec` failed because a combined two-term sum is not a contiguous subterm of the left-associative larger sum. Fix: split into `h_tang1`/`h_tang2` (one per summand), mirroring the x-file's own `h_tang1`/`h_tang2` split exactly. Recorded in full in `proof-run-log.md` (attempt 2 for `PixelIffHelpersY.lean`).

A second, new-to-this-slice hard step: a hypothesis-name collision (`h` meaning both "sensor height" and, in the x-file's naming convention, "the universal pixel-equality hypothesis"). This did not occur in the x-slice because its sensor-dimension variable is named `w`, not `h` — a direct consequence of the project's own established `h, h_shader` y-axis naming (`principal_point_conversion_2d_iff`) colliding with the x-file's hypothesis-naming convention when mirrored naively. Resolved by renaming the hypothesis to `hpx`. Recorded in `proof-run-log.md`.

## Discrimination / Anti-Vacuity Result (required by the MAPS handoff)

Two categories of y-axis mutation theorem added in `MutationTestsY.lean`, both via a new local extraction lemma `whole_tangential_field_iff_y` (specialization points `(1,0)` and `(1,1)`, re-derived by hand for the y-term shape, not copied from the x-version's `(0,1)`/`(1,0)`/`(1,1)` — see `proof-plan.md`):

1. **Wrong F-power** (`wrong_q1_power_F4_forces_power_degeneracy_y` / `_inconsistent_y`): `q1 = p1/F⁴` instead of the correct `p1/F²` forces the degenerate condition `F²=F⁴`.
2. **Coefficient swap** (`wrong_q1_paired_with_p2_forces_coincidence_y` / `_inconsistent_y`): pairing `q1` with `p2` instead of `p1` forces `p1=p2`, an almost-always-false arithmetic coincidence.

Both discriminate correctly: a materially wrong conversion (wrong power, or wrong coefficient pairing) is proved inconsistent, not merely "not proved consistent." This satisfies the handoff's "at least 2" requirement with the two specifically requested categories.

## Anti-Pattern Scan

- No broad automation hiding the hard step: the `linear_combination` expression in `pixel_eq_implies_tangential_gap_y` is explicit, same structure as the x-version.
- No proxy property: the theorems directly state and prove `h_shader/h = fy` extraction (sufficiency theorem) and pixel agreement (iff theorem), matching the handoff's "exact intended claim" verbatim.
- No vacuous hypothesis: `hp` is non-trivially used in `tangential_gap_forces_scale_y`; `hwrong` in each mutation theorem is used, not merely declared.
- No unauthorized definition changes: no existing file touched.
- No import creep: `PixelSufficiencyY.lean`/`PixelIffHelpersY.lean` import only `DistortionConversion` (same as the x-files); `PixelIffY.lean` imports only the two new sibling files (same pattern as `PixelIff.lean`); `MutationTestsY.lean` imports `Mathlib.Tactic` + `DistortionConversion` (same as `MutationTests.lean`).
- No `field_simp`/`ring_nf` on a full pixel equation: applied only to small helper goals throughout.
- Did **not** fold in `DistortionConversionCorrected.lean`'s alternative tangential formula, per the handoff's explicit instruction — confirmed by grep: no reference to `DistortionConversionCorrected` anywhere in the 4 new files.
- Did **not** attempt to derive `denominatorNonzero` from coefficient bounds — it remains a free hypothesis in both new theorems, unchanged from the x-case.

## Warnings (Non-Blocking)

- Unused variable `hF_pos` in `PixelSufficiencyY.lean` — pre-existing pattern, same as the x-sibling (`PixelSufficiency.lean:34`), kept for hypothesis-list parity with the iff theorem's ← direction call site.
- Unused variable `hden` in `radial_ratio_scaled_eq_y` — pre-existing pattern, same as the x-sibling's `radial_ratio_scaled_eq`.
- Unused variables `hh`, `hhs` in `principal_offset_cancels_y` — pre-existing pattern, same as the x-sibling's `principal_offset_cancels`.

None of these affect correctness; all mirror an already-accepted warning category in the x-axis files, not a new issue introduced by this slice.

## Reusable Technique Check

```
REUSABLE TECHNIQUE CHECK:
- Technique name: Mechanical axis-mirroring via confirmed variable/coefficient substitution
- Applicability conditions: proofs over symmetric x/y pixel-pipeline claims where the two
  axes are mathematically equivalent except for which tangential coefficient plays which role
- Lean approach: re-derive axis-invariant local `have`s verbatim; re-specialize helper lemmas'
  point choices by hand-deriving from the actual swapped term shape (confirmed in proof-capsule.md
  before writing any Lean); keep new files self-contained rather than reusing existing lemmas via
  argument-order tricks (rejected as fragile in proof-plan.md, confirmed fragile in practice by the
  hypothesis-naming collision this slice hit when mirroring too literally)
- Recorded in proof-plan.md: yes
- Recorded in proof-review.md: yes (this file)
```

## Conclusion

The proof is complete. `opencv_openlensio_full_pipeline_pixel_sufficiency_y` and `opencv_openlensio_full_pipeline_pixel_iff_y` are fully proved, no `sorry` remains anywhere in the 4 new files, the proof is kernel-checked (full project `lake build` succeeds), both hard steps are explicitly recorded with their resolutions, the statements match the MAPS handoff's exact intended claim, the required discrimination check is satisfied with both requested mutation categories, and no forbidden constructs are present. PROP-003's y-pixel residual gap (`property-register.md`) and EVID-006 (`evidence-matrix.md`) are ready to be updated to reflect this realized evidence.
