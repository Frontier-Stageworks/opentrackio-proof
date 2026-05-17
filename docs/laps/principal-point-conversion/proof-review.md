---
name: principal-point-conversion-proof-review
description: Adopted proof review for PrincipalPointConversion.lean
metadata:
  type: project
---

# Adopted Proof Review

This proof was written before LAPS or outside the LAPS workflow.

The review backfills LAPS artifacts for future maintenance. It does not imply the proof was originally developed under LAPS.

---

## Lean check

```sh
lake env lean opencv_opentrackio_proofs/PrincipalPointConversion.lean
```

**Result:** Clean (no output). 2026-05-16.

---

## Theorem inventory

| Theorem | Statement status | Proof status | Risk | Recommended next action |
|---------|-----------------|--------------|------|------------------------|
| `principal_point_conversion_necessary` | Accepted | Compiles — point specialisation + nlinarith | Low | Accept as-is |
| `principal_point_conversion_iff` | Accepted | Compiles — constructor pair delegating to Theorem 1 | Low | Accept as-is |
| `principal_point_conversion_2d_iff` | Accepted | Compiles — axis decomposition + Theorem 2 twice | Low | Accept as-is |
| `single_focal_length_compatibility` | Accepted with notes | Compiles — delegation + linarith | Low | Accept as-is; note parameter bloat |
| `buggy_principal_point_conversion_inconsistent` | Accepted | Compiles — contradiction via scale nonzero-ness | Low | Accept as-is |

---

## Per-theorem review

### `principal_point_conversion_necessary`

**Proof strategy:** Point specialisation + linear system solution.

**Hard step:** `field_simp [hw, hw_s]` clears denominators, converting the two specialised equations into a polynomial system. `nlinarith` then closes each of the two components by combining h0 and h1. The field_simp output (clearing `w` and `w_shader` from denominators) is the essential step that makes nlinarith feasible.

**Anti-pattern scan:**

| Anti-pattern | Present? |
|---|---|
| Tactic soup | No — three logical phases: specialise, clear denominators, solve |
| Automation hiding hard step | Mild note — `nlinarith` closes a bilinear system; the hard work is in field_simp's normalization |
| Over-strong hypotheses | No |
| Unused hypotheses | No |
| Vacuity | No |

**Mathlib upgrade robustness:** The `field_simp [hw, hw_s]` + `nlinarith` pattern is stable. If `nlinarith` ever stops closing these (unlikely — the system is 2×2 and linear after clearing denominators), replacing with `linarith` after `ring_nf` would work.

**Verdict:** Accepted as-is.

---

### `principal_point_conversion_iff`

**Proof strategy:** Constructor pair — Theorem 1 for `→`, explicit `ring` proof for `←`.

**Hard step:** The `←` direction: `rw [hF, hΔPx]; field_simp [hw, hw_s]; ring`. After rewriting and clearing denominators, `ring` closes the algebraic identity.

**Anti-pattern scan:** None.

**Verdict:** Accepted as-is.

---

### `principal_point_conversion_2d_iff`

**Proof strategy:** Axis decomposition — reduce to two independent 1D problems using Theorem 2.

**Hard step:** The decomposition `fun x'' => (hconsist x'' 0).1` is the key insight. Specialising y''=0 decouples the x-axis equation. Without this, the 2D problem would require a more complex argument.

**Anti-pattern scan:**

| Anti-pattern | Present? |
|---|---|
| Tactic soup | No — clean four-step proof |
| Unused hypotheses | No |
| Proxy property | No |

**Verdict:** Accepted as-is.

---

### `single_focal_length_compatibility`

**Proof strategy:** Delegation to Theorem 3 + linarith.

**Hard step:** None beyond the delegation. `obtain ⟨hFx, _, hFy, _⟩` discards the ΔPx and ΔPy equations (wildcards) and keeps the F equations; `linarith` closes immediately.

**Anti-pattern note — parameter bloat:**
`cx`, `cy`, `ΔPx`, `ΔPy` appear in the theorem signature but not in the conclusion. They are required because `principal_point_conversion_2d_iff` is applied to `hconsist`, and that theorem carries all parameters. This is not a proof anti-pattern, but a future maintainer might find the signature noisy.

A refactor option: existentially abstract `ΔPx`, `ΔPy`, `cx`, `cy` out of the conclusion. But this would change the theorem statement and require user authorization. The current form is correct.

**Verdict:** Accepted as-is. Refactor of parameter bloat is optional — low priority.

---

### `buggy_principal_point_conversion_inconsistent`

**Proof strategy:** Contradiction — extract `hΔPx` from Theorem 1, combine with `hbug`, derive `(w/w_shader)*(w_shader/2) = 0`, case-split on `mul_eq_zero`, close each branch.

**Hard step:** The algebraic combination:
- `hΔPx : ΔPx = (w/w_shader)*(cx - w_shader/2)`
- `hbug  : ΔPx = (w/w_shader)*cx`
- Together force `(w/w_shader)*(w_shader/2) = 0` — derived by `linarith`.

Then `mul_eq_zero.mp hws2` gives two cases:
- `w/w_shader = 0` — contradicts `div_ne_zero hw hw_s` via `absurd`
- `w_shader/2 = 0` — `linarith` gives `w_shader = 0`, contradicts `hw_s`

**Anti-pattern scan:**

| Anti-pattern | Present? |
|---|---|
| Tactic soup | No — five steps, each purposeful |
| Over-strong hypotheses | No — `hw` and `hw_s` are both necessary |
| Vacuity | No — the proof constructs an actual contradiction |
| Proxy property | No — concludes `False`, not a weaker consequence |
| Arbitrary case split | No — `mul_eq_zero` is the natural case split here |

**Why direct contradiction (not forces-degeneracy)?**
The MutationTests adoption confirms this is the unique mutation theorem where the contradiction is unconditional. The buggy formula `ΔPx = (w/w_shader)*cx` forces `(w/w_shader)*(w_shader/2) = 0`, and since `w/w_shader ≠ 0` (from `w ≠ 0` and `w_shader ≠ 0`), the only escape would require `w_shader = 0`, which is excluded. There is no non-degenerate case where the buggy formula is consistent.

**Verdict:** Accepted as-is.

---

## Dependency analysis

```
principal_point_conversion_necessary   ← root lemma
  └─ principal_point_conversion_iff    ← builds iff from necessity + ring
       └─ principal_point_conversion_2d_iff   ← decomposes 2D into two 1D
            └─ single_focal_length_compatibility  ← corollary via linarith
principal_point_conversion_necessary
  └─ buggy_principal_point_conversion_inconsistent  ← contradiction branch
```

The dependency tree is shallow and clean. `principal_point_conversion_necessary` is the only theorem that does real arithmetic work (`nlinarith`). All other theorems are structural above it.

---

## Cross-file usage

`principal_point_conversion_necessary` is used directly in:
- `MutationTests.lean` — sections A, B, C, D, E
- `PixelEquivalence.lean` — indirectly via `principal_point_conversion_2d_iff`

`principal_point_conversion_2d_iff` is exported to `PixelEquivalence.lean` as `linear_projection_pixel_equivalence_2d_iff`.

`buggy_principal_point_conversion_inconsistent` is re-exported in `MutationTests.lean` as `buggy_projection_offset_missing_center_inconsistent`.

---

## Overall verdict

**All five theorems: accepted as-is.** No repair or refactor required.

Optional future work (not urgent):
- Refactor `single_focal_length_compatibility` to drop the unused parameters `cx`, `cy`, `ΔPx`, `ΔPy` from the signature — would require a statement change and user authorization.
- Document the `nlinarith` proof certificate for `principal_point_conversion_necessary` if Mathlib upgrade robustness becomes a concern.
