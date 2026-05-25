---
name: nonconstructive-left-inverse-metrics
description: Process metrics for the nonconstructive left-inverse campaign
metadata:
  type: reference
---

# Metrics — Nonconstructive Left Inverse Campaign

**Task slug:** `nonconstructive-left-inverse`
**Date started:** 2026-05-25
**Repo commit at start:** `494947f8f84032390c560148d87fe8ce2c115a87`
**Model:** claude-sonnet-4-6
**Command:** `laps-start`
**Task bucket:** theorem proving / mathematical property
**Task size:** medium

---

## Baseline Expected Artifacts

- proof-capsule.md ✓
- statement-audit.md ✓
- ambiguity-register.md ✓
- proof-plan.md ✓
- metrics.md ✓ (this file)
- proof-run-log.md: pending (Stop 3, during NCL-00 implementation)
- proof-review.md: pending (Stop 4, after NCL-01)

---

## Slice Tracking

| Slice | Status | Lean check | Semantic failures | Human interventions | Sorry at any point |
|---|---|---|---|---|---|
| NCL-00 | complete | exit 0, no warnings | 0 | 0 | no |
| NCL-01 | complete | exit 0, no warnings | 0 | 0 | no |

---

## Process Events

| Date | Event | Notes |
|---|---|---|
| 2026-05-25 | laps-start complete | Stop 1 artifacts created; 4 AMBs registered; NCL-00 selected as first slice |
| 2026-05-25 | NCL-00 complete | Compiled first attempt; exit 0; DomainPoint, undistortSub, domainPoint_nonempty, undistortSub_injective_pure_radial all accepted |
| 2026-05-25 | NCL-01 complete | Compiled first attempt; exit 0; Function.leftInverse_invFun one-liner; lake build confirmed |

---

## Final Score

**Campaign complete.** Both slices (NCL-00, NCL-01) accepted.

| Metric | Value |
|---|---|
| Total Lean checks | 2 (one per slice, both same lake env lean invocation) |
| Checks passing on first attempt | 2 / 2 |
| Semantic failures | 0 |
| Human interventions | 0 |
| Sorry at any point | no |
| AMB entries resolved | 2 (AMB-NCL-001, AMB-NCL-002) |
| AMB entries carried forward | 2 (AMB-NCL-003 — hScaleInj open; AMB-NCL-004 — left-only scope) |
| New theorems | 2 (undistortSub_injective_pure_radial, undistortSub_nonconstructive_left_inverse_pure_radial) |
| New definitions | 2 (DomainPoint, undistortSub) |
| New instances | 1 (domainPoint_nonempty) |
| Key Mathlib lemma correction | proof-plan.md predicted Function.Injective.invFun_apply; actual lemma is Function.leftInverse_invFun |
| Stop conditions fired | 0 |
