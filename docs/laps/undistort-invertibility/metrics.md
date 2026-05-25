---
name: undistort-invertibility-metrics
description: Process metrics for the undistort invertibility campaign
metadata:
  type: reference
---

# Metrics — Undistort Invertibility Campaign

**Task slug:** `undistort-invertibility`
**Date started:** 2026-05-24
**Repo commit at start:** unknown (run `git rev-parse HEAD` to record)
**Model:** claude-sonnet-4-6
**Command:** `laps-start`
**Task bucket:** theorem proving / mathematical property
**Task size:** large

---

## Baseline Expected Artifacts

- proof-capsule.md ✓
- statement-audit.md ✓
- ambiguity-register.md ✓
- work-queue.md ✓
- first-slice-contract.md ✓
- metrics.md ✓ (this file)
- proof-plan.md: pending (Stop 2, before first slice implementation)
- proof-run-log.md: pending (Stop 3, during first slice)
- proof-review.md: pending (Stop 4, after first slice)

---

## Slice Tracking

| Slice | Status | Lean check | Semantic failures | Human interventions | Sorry at any point |
|---|---|---|---|---|---|
| SLICE-UI-00 | complete | exit 0, no warnings | 0 | 0 | no |
| SLICE-UI-01 | complete | exit 0, no warnings | 0 | 0 | no |
| SLICE-UI-02 | complete | exit 0, no warnings | 0 | 0 | no |
| SLICE-UI-03 | complete | exit 0, no warnings | 0 | 0 | no |
| SLICE-UI-04 | complete | exit 0, no warnings | 0 | 0 | no |

---

## Process Events

| Date | Event | Notes |
|---|---|---|
| 2026-05-24 | laps-start complete | Stop 1 artifacts created; LARGE TASK STOP emitted; awaiting user authorization for UI-00 |
| 2026-05-24 | SLICE-UI-00 complete | Proof compiled first attempt; exit 0; Stop 4 review accepted |
| 2026-05-24 | SLICE-UI-01 complete | Proof compiled first attempt; exit 0; Stop 4 review accepted |
| 2026-05-24 | SLICE-UI-02 complete | Proof compiled first attempt; exit 0; Stop 4 review accepted; AMB-UI-003 resolved |
| 2026-05-24 | SLICE-UI-03 complete | Proof compiled first attempt; exit 0; Stop 4 review accepted; Jacobian TBD resolved via algebraic det |
| 2026-05-24 | SLICE-UI-04 complete | Proof compiled first attempt; exit 0; Stop 4 review accepted; AMB-UI-005 resolved; AMB-UI-001 reflected in explicit r param |

---

## Final Score

**Campaign complete.** All five slices (UI-00 through UI-04) accepted.

| Metric | Value |
|---|---|
| Total Lean checks | 5 (one per slice) |
| Checks passing on first attempt | 5 / 5 |
| Semantic failures | 0 |
| Human interventions | 0 |
| Sorry at any point | no |
| AMB entries resolved | 3 of 5 (AMB-UI-003, AMB-UI-004 via alternate approach, AMB-UI-005) |
| AMB entries partially resolved | 2 (AMB-UI-001 reflected; AMB-UI-002 partially addressed) |
| New theorems | 6 |
| New definitions | 3 (radialScale, radialDescale, and bridge lemma radialTerm_eq_radialScale) |
| Stop conditions fired | 0 |
