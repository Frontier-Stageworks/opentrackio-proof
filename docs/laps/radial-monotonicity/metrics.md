---
name: radial-monotonicity-metrics
description: Metrics for the radial-monotonicity campaign (RM-00 through RM-02)
metadata:
  type: reference
---

# Metrics — Radial Term Monotonicity

**Task slug:** `radial-monotonicity`
**Date started:** 2026-05-25
**Date completed:** 2026-05-25
**Model:** claude-sonnet-4-6
**Repo commit at start:** `a56f8eb67c2de4f3bb27acbd10fb08c5d88ebd5a`

---

## Theorem Inventory

| ID | Declaration | Status | First-attempt |
|---|---|---|---|
| RM-00 | `private lemma radialScale_mul_derivPos` | ✓ Complete | No — ordering issue, 2 edits |
| RM-01 | `theorem radialScale_mul_strictMono` | ✓ Complete | Yes |
| RM-02 | `theorem radialScale_hScaleInj` | ✓ Complete | Yes |

---

## Lean Attempt Log

| Attempt | Slice | Result | Notes |
|---|---|---|---|
| 1 | RM-00 | Error: `No goals to be solved` at `ring` | `simp only [numFun]` + `convert h3 using 1` closed all goals, leaving `ring` with nothing; fixed by using `exact h2.add h_k5r7` for h_num and removing simp from h_den |
| 2 | RM-00 | Error: `radialScale_mul_derivPos` already declared | RM-00 was inserted after NCL-00 while RM-01/02 were inserted before NCL-00; duplicate when fixed; fixed by removing original placement |
| 3 | All | `lake env lean InjectivityModel.lean` exit 0 | All three slices clean |
| 4 | All | `lake build InjectivityModel` exit 0 | Full build clean |

---

## Failure Classification

| Category | Count |
|---|---|
| Proof stops | 0 |
| Algebra stops | 0 |
| Conceptual stops | 0 |
| Human interventions | 1 (user redirected focus to RM-00 after exploration overrun) |
| Tactic failures | 1 (`ring` with no goals — `simp`+`convert` interaction) |
| Ordering/structural errors | 1 (duplicate declaration from wrong insertion position) |

---

## Ambiguity Resolution

| ID | Issue | Resolution |
|---|---|---|
| AMB-RM-003 | Squaring injectivity lemma | Resolved: `pow_left_inj₀` in `Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic` |
| AMB-RM-004 | HasDerivAt.deriv interface | Resolved: `HasDerivAt.deriv : HasDerivAt f f' x → deriv f x = f'` in Basic.lean:435 |

---

## Actual vs. Planned Proof Shapes

| Slice | Planned | Actual |
|---|---|---|
| RM-00 | `HasDerivAt` chain + `HasDerivAt.div` + `nlinarith` | As planned; `h_num` via `exact h2.add h_k5r7` (term-mode); `h_den` via `convert + ring` |
| RM-01 | `strictMonoOn_of_deriv_pos` + `ContinuousOn.div` + `interior_Ici` | As planned; `fun_prop` handled numerator/denominator continuity |
| RM-02 | `ring` rewrite + `pow_left_inj₀` + `StrictMonoOn.injOn` | As planned |

---

## Artifact Discipline

| Artifact | Status |
|---|---|
| proof-capsule.md | ✓ Complete |
| statement-audit.md | ✓ Complete |
| ambiguity-register.md | ✓ Complete (all 4 ambiguities resolved) |
| proof-plan.md | ✓ Complete |
| metrics.md | ✓ This file |
| proof-review.md | Pending |

---

## Lean Verification Evidence

**Per-file check:**
```
lake env lean openlensio_semantics/InjectivityModel.lean
# exit 0, no warnings
```

**Full build:**
```
lake build InjectivityModel
# ✔ [3289/3290] Built InjectivityModel (4.1s) — exit 0
```

---

## Final Score

Campaign complete. 3 declarations added (1 private lemma + 2 public theorems).
No sorry, axiom, unsafe, or partial used.
Whole-repo total: 147 + 3 = **150 declarations**.
