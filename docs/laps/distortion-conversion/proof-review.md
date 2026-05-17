---
name: distortion-conversion-proof-review
description: Adopted proof review for DistortionConversion.lean
metadata:
  type: project
---

# Adopted Proof Review

This proof was written before LAPS or outside the LAPS workflow.

The review backfills LAPS artifacts for future maintenance. It does not imply the proof was originally developed under LAPS.

---

## Lean check

```sh
lake env lean opencv_opentrackio_proofs/DistortionConversion.lean
```

**Result:** Clean (no output). 2026-05-16.

---

## Theorem inventory

| Theorem | Statement status | Proof status | Risk | Recommended next action |
|---------|-----------------|--------------|------|------------------------|
| `radial_distortion_conversion` | Accepted | Compiles — point specialisation + linarith | Low | Accept as-is |
| `tangential_q1_conversion` | Accepted | Compiles — point specialisation + nlinarith | Low | Accept as-is |
| `tangential_q2_conversion` | Accepted | Compiles — point specialisation + nlinarith | Low | Accept as-is |
| `whole_radial_polynomial_iff` | Accepted | Compiles — Vandermonde specialisation + refine <;> nlinarith | Low | Accept as-is |
| `whole_tangential_field_iff` | Accepted | Compiles — overdetermined specialisation + refine <;> nlinarith | Low | Accept as-is |
| `whole_tangential_field_2d_iff` | Accepted | Compiles — delegation to Theorem 5 + field_simp | Low | Accept as-is |
| `all_distortion_conversions_iff` | Accepted | Compiles — three rw + conjunction rearrangement | Low | Accept as-is |
| `radial_coefficients_imply_rational_factor_equality` | Accepted | Compiles — linarith + rw | Low | Accept as-is |

---

## Per-theorem review

### `radial_distortion_conversion`

**Proof strategy:** Point specialisation + linear system solution.

**Hard step:** `pow_ne_zero _ hF` producing `hFn` to enable `field_simp [hFn]`. After clearing the `F^(2n)` denominator, `linarith` closes from the specialised hypothesis `k = l * F^(2n)`.

**Anti-pattern scan:**

| Anti-pattern | Present? |
|---|---|
| Tactic soup | No — three logical phases: specialise, clear denominators, close |
| Automation hiding hard step | No — field_simp normalises denominator; linarith closes a linear equation |
| Over-strong hypotheses | No |
| Unused hypotheses | No |
| Vacuity | No |

**Note on generality:** Valid for any `n : ℕ` including `n = 0` (gives `l = k`). The paper only uses n=1,2,3 but the general form is cleaner and more reusable.

**Verdict:** Accepted as-is.

---

### `tangential_q1_conversion`

**Proof strategy:** Point specialisation at `(x', y') = (1, 1)` + nlinarith.

**Hard step:** `nlinarith [sq_nonneg F]` — after `field_simp`, the goal involves `F^2` products. The `sq_nonneg F` hint (i.e., `0 ≤ F^2`) provides the orientation nlinarith needs to close the quadratic rather than relying on linarith.

**Anti-pattern scan:** None.

**Verdict:** Accepted as-is.

---

### `tangential_q2_conversion`

**Proof strategy:** Point specialisation at `(r, x') = (1, 0)` + nlinarith.

**Hard step:** Same `nlinarith [sq_nonneg F]` pattern.

**Note on hypothesis:** `hconsist` universally quantifies over independent `r` and `x'`. This is stronger than the geometric constraint `r^2 = x'^2 + y'^2`, which is appropriate for a polynomial identity proof. The witness `(r=1, x'=0)` is geometrically realizable, as documented in the file comment.

**Anti-pattern scan:** None.

**Verdict:** Accepted as-is.

---

### `whole_radial_polynomial_iff`

**Proof strategy:** Vandermonde-style point specialisation (→) + rewrite (←).

**Hard step:** `norm_num at h2 h3` evaluates the powers at `r=2` and `r=3` to concrete integers (4, 16, 64 and 9, 81, 729 respectively). Without this, `nlinarith` would face symbolic power terms it cannot compare. After norm_num, the three equations form a fully numeric linear system that `nlinarith` closes for each of the three coefficient goals.

**Anti-pattern scan:**

| Anti-pattern | Present? |
|---|---|
| Tactic soup | No — three logical phases: specialise, evaluate, close |
| `<;>` misuse | No — `refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> nlinarith` generates three same-shape goals, each closed by the same tactic chain using h1, h2, h3 in context |
| Automation hiding hard step | Mild note — `nlinarith` closes a 3×3 linear system; the hard work is in `norm_num`'s evaluation and `field_simp`'s normalisation |
| Over-strong hypotheses | No |
| Unused hypotheses | No |

**Mathlib upgrade robustness:** `norm_num` + `field_simp` + `nlinarith` is a stable combination. If nlinarith ever fails (unlikely — system is linear after preprocessing), replacing with `linarith` after additional `ring_nf` would work.

**Verdict:** Accepted as-is.

---

### `whole_tangential_field_iff`

**Proof strategy:** Overdetermined point specialisation (→) + rewrite (←).

**Hard step:** Three specialisations `(0,1)`, `(1,0)`, `(1,1)` give 3 equations for 2 unknowns. `norm_num` evaluates them; `nlinarith` closes both goals using the overdetermined system.

**Anti-pattern scan:**

| Anti-pattern | Present? |
|---|---|
| Tactic soup | No — same three-phase structure as Theorem 4 |
| `<;>` misuse | No — two same-shape goals, same tactic chain |
| Automation hiding hard step | Mild note — same as Theorem 4 |
| Over-strong hypotheses | No |
| Unused hypotheses | No |

**Note on δx only:** The theorem requires consistency of δx alone. This is sufficient because the δx polynomial in (x', y') uniquely determines both q1 and q2. The 2D version (Theorem 6) completes the picture for the full vector field.

**Verdict:** Accepted as-is.

---

### `whole_tangential_field_2d_iff`

**Proof strategy:** Delegation to `whole_tangential_field_iff` (→) + delegation + ring (←).

**Hard step:** None beyond the delegation. The insight is that δx alone suffices: `(h x' y').1` extracts the δx component from the 2D hypothesis. The δy direction in `←` is mechanical: `rw [hq1, hq2]; field_simp` verifies the algebraic identity.

**Anti-pattern scan:**

| Anti-pattern | Present? |
|---|---|
| Tactic soup | No — clean four-line proof |
| Statement laundering | No — strictly stronger hypothesis (2D) than Theorem 5 (1D), same conclusion; intentional design |
| Unused hypotheses | No — the δy component is used in the ← direction |

**Verdict:** Accepted as-is.

---

### `all_distortion_conversions_iff`

**Proof strategy:** Three-rewrite delegation + conjunction rearrangement.

**Hard step:** None. After `rw [whole_radial_polynomial_iff ..., whole_radial_polynomial_iff ..., whole_tangential_field_2d_iff ...]`, the goal is a pure conjunction restructuring. The `constructor` + two `exact` branches flatten nested triples and pairs into a flat 8-tuple.

**Anti-pattern scan:**

| Anti-pattern | Present? |
|---|---|
| Tactic soup | No — one compound rw + constructor |
| Automation hiding hard step | N/A — no automation; structural proof |
| Weakened conclusion | No — all eight conversions appear in the conclusion |
| Unused hypotheses | No |

**Note on parameter naming:** `k4,k5,k6` are OpenCV denominator coefficients; `l2,l4,l6` are OpenTrackIO denominator coefficients (even-indexed `l`). The naming mirrors the SMPTE paper. The interleaving (odd `l` = numerator, even `l` = denominator) is potentially confusing for a first reader but consistent throughout the file.

**Verdict:** Accepted as-is.

---

### `radial_coefficients_imply_rational_factor_equality`

**Proof strategy:** Linear combination (linarith) + rewrite.

**Hard step:** None. `linarith` trivially adds 1 to `hnum` and `hden`; `rw [hn_cv, hd_cv]` closes by definitional equality.

**Anti-pattern scan:**

| Anti-pattern | Present? |
|---|---|
| Tactic soup | No — two linarith derivations + rw |
| Weakened conclusion | No — one-way is the correct direction; the file comment explicitly documents why the converse is false |
| Missing ∀r? | Fixed-r form is correct granularity for pointwise use; ∀r corollary is trivial but not needed |
| Missing nonzero denominator hypothesis? | Correct — the file comment explains that ℝ division equality holds syntactically when both num and den are equal, without `≠ 0` |

**Verdict:** Accepted as-is.

---

## Dependency analysis

```
radial_distortion_conversion     ← Layer 1 root (imported by MutationTests, PixelEquivalence)
tangential_q1_conversion         ← Layer 1 root (imported by MutationTests)
tangential_q2_conversion         ← Layer 1 root (imported by MutationTests)

whole_radial_polynomial_iff      ← Layer 2 (independent within file)
  └─ all_distortion_conversions_iff

whole_tangential_field_iff       ← Layer 2
  └─ whole_tangential_field_2d_iff
       └─ all_distortion_conversions_iff

radial_coefficients_imply_rational_factor_equality  ← standalone corollary
```

Layer 1 and Layer 2 theorems are independent within this file. The whole-polynomial
theorems re-derive their results via Vandermonde specialisation rather than delegating
to the per-term Layer 1 theorems. Both derivation paths are correct; Layer 1 is
exported as lemmas for downstream files.

---

## Cross-file usage

- `radial_distortion_conversion` — used in `MutationTests.lean` sections D (radial wrong-power mutations) and in `PixelEquivalence.lean` (`radial_distortion_value_equivalence`)
- `tangential_q1_conversion`, `tangential_q2_conversion` — used in `MutationTests.lean` sections F, G, H (tangential mutations)
- `whole_radial_polynomial_iff`, `whole_tangential_field_iff`, `whole_tangential_field_2d_iff` — available for downstream use; currently imported by `MutationTests.lean` via its `import DistortionConversion`
- `all_distortion_conversions_iff`, `radial_coefficients_imply_rational_factor_equality` — currently no direct external users; available for future pipeline theorems

---

## Overall verdict

**All eight theorems: accepted as-is.** No repair or refactor required.

Optional future work (not urgent):
- Add `ring` fallback after `field_simp` calls in `←` directions (Mathlib upgrade robustness, low priority — same note as in `PixelEquivalence.lean` review).
- Add a `∀r` wrapper theorem around `radial_coefficients_imply_rational_factor_equality` if full-pipeline composition theorems are later added.
- Add a theorem relating `all_distortion_conversions_iff` to the full rational correction factor equality (currently only the pointwise Theorem 8 exists for this).
