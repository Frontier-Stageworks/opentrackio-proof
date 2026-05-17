---
name: pixel-equivalence-proof-review
description: Adopted proof review for PixelEquivalence.lean
metadata:
  type: project
---

# Adopted Proof Review

This proof was written before LAPS or outside the LAPS workflow.

The review backfills LAPS artifacts for future maintenance. It does not imply the proof was originally developed under LAPS.

---

## Lean check

```sh
lake env lean opencv_opentrackio_proofs/PixelEquivalence.lean
```

**Result:** Clean (no output). 2026-05-16.

---

## Theorem inventory

| Theorem | Statement status | Proof status | Risk | Recommended next action |
|---------|-----------------|--------------|------|------------------------|
| `linear_projection_pixel_equivalence_2d_iff` | Accepted | Compiles — term-mode delegation | Low | Accept as-is |
| `radial_distortion_value_equivalence` | Accepted with notes | Compiles — field normalization + transport | Low | Accept as-is |

---

## Per-theorem review

### `linear_projection_pixel_equivalence_2d_iff`

**Proof strategy:** Theorem delegation (single-term proof).

**Hard step:** None.

**Anti-pattern scan:**

| Anti-pattern | Present? |
|---|---|
| Statement laundering | No — named alias in pipeline vocabulary; same strength as the delegated theorem |
| Vacuity | No |
| Weakened conclusion | No — iff |
| Over-strong hypotheses | No |
| Unused hypotheses | No |
| Proxy property | No |
| Tactic soup | N/A — term proof |
| Automation hiding hard step | N/A |

**Verdict:** Accepted as-is. Clean, zero-cost delegation. The purpose of this theorem is vocabulary: renaming `x''`/`y''` to `x`/`y` and framing the statement as a pipeline equivalence rather than a parameter characterization. This is valid documentation-level value.

---

### `radial_distortion_value_equivalence`

**Proof strategy:** Equality transport + field normalization.

Breakdown:
1. `pow_ne_zero _ hF` × 3 — derive `F^2`, `F^4`, `F^6` nonzero-ness. **Definitional reduction.**
2. `rw [hl1, hl3, hl5]; field_simp [hF2, hF4, hF6]` — substitute coefficients, cancel `F^(2n)` factors. **Field normalization.**
3. `rw [hl2, hl4, hl6]; field_simp [hF2, hF4, hF6]` — same for denominator. **Field normalization.**
4. `hden ▸ hden_cv` — transport `≠ 0` along denominator equality. **Theorem delegation (Eq.mpr).**
5. `⟨by rw [hnum, hden], hden_oti⟩` — assemble conjunction. **Constructor-driven proof.**

**Hard step:** `field_simp [hF2, hF4, hF6]` fully closing `(ki/F^(2n)) * (F*r)^(2n) = ki*r^(2n)`. This is not trivial algebraically — it requires clearing denominators and cancelling power factors — but `field_simp` handles it without a `ring` follow-up.

**Anti-pattern scan:**

| Anti-pattern | Present? |
|---|---|
| Statement laundering | No |
| Vacuity | No |
| Weakened conclusion | No — one-way is correct (see note) |
| Over-strong hypotheses | No |
| Unused hypotheses | No — all six hli used in rw; hF used for pow_ne_zero; hden_cv used for transport |
| Proxy property | No |
| Tactic soup | No — 4 distinct logical steps, each purposeful |
| `field_simp` hiding hard step | Mild note — see below |
| Algebra ping-pong | No |

**Note on `field_simp` closing the goal directly:**
`field_simp [hF2, hF4, hF6]` after `rw [hli ...]` closes the subgoal without `ring`. This means `field_simp` is fully normalizing both sides. This is not an anti-pattern but is worth noting for Mathlib upgrade robustness: if a future Mathlib version changes `field_simp` normalization and leaves a residual `ring` goal, the proof will break at these two lines. The fix is trivial (add `ring`). Risk: **Low**.

**Note on one-way implication:**
The theorem is `hprem → conclusion`, not an iff. This is correct: the coefficient equations are the hypothesis; rational factor equality is a consequence. The converse (rational factor equality → coefficient equations) is false in general because equal rational functions can have different coefficients. The one-way direction is not a weakening — it is the correct logical direction.

**Verdict:** Accepted as-is.

---

## Scope limitation review

The file header explicitly documents that full end-to-end pipeline equivalence (linear projection + distortion) is deferred. The documented reason is sound: OpenCV and OpenTrackIO tangential terms operate in different spaces (normalised vs. screen), and after parameter conversion the tangential pixel contribution in each model differs unless `ws/w = fx`. This condition is not generally true.

This is an honest scope limitation, not a proof gap. The two theorems in the file cover the portions of the pipeline where equivalence is cleanly characterized. The deferred work requires a joint specification of how tangential distortion output feeds into the final pixel coordinate in each model.

**Future work ticket (not a blocker):** If the SMPTE paper is updated to specify the full composition semantics, a third theorem `tangential_distortion_pixel_equivalence` could be added to complete the pipeline.

---

## Recommended next action

**Both theorems: accept as-is.** No repair or refactor needed.

Optional future work (not urgent):
- Add `ring` fallback after `field_simp` calls (Mathlib upgrade robustness, low priority)
- Add the full pipeline composition theorem if the paper's composition semantics are later specified
