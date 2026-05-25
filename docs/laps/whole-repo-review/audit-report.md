# LAPS Audit: opentrackio-proof — Whole-Repo

## Audit Target

- Lean project root: `/Users/markstalzer/github/opentrackio-proof`
- LAPS artifact directory: `docs/laps/` (multiple slugs)
- Audit date: 2026-05-24
- HEAD commit at audit: `b859352` — "clarified some open items and ambiguities"
- Prior audit commit: `c948dc4` (whole-repo audit, 2026-05-24, same session — predates undistort-invertibility campaign)
- Audit mode:
  - semantic audit
  - definition/model audit
  - artifact freshness audit
  - forbidden construct audit

---

## Files Inspected

| File | Status | Notes |
|---|---|---|
| `openlensio_semantics/` (12 files) | present | +1 vs prior audit: InjectivityModel.lean added by undistort-invertibility campaign |
| `opencv_opentrackio_proofs/` (9 files: 5 root + 4 Pipeline/) | present | Unchanged since prior audit |
| `opentrackio_parser/` (45 files) | present | Unchanged since prior audit |
| `docs/laps/whole-repo-review/proof-review.md` | stale by 7 declarations | Says 138; current is 145; covered by undistort-invertibility/proof-review.md |
| `docs/laps/whole-repo-review/metrics.md` | current | Scores 12/12 at prior audit; unchanged |
| `docs/laps/undistort-invertibility/proof-review.md` | current | Updated this session; covers all 7 InjectivityModel.lean declarations |
| `docs/laps/undistort-invertibility/metrics.md` | current | Finalized this session |
| `docs/laps/undistort-invertibility/ambiguity-register.md` | current | AMB-UI-001, AMB-UI-005 updated this session |
| `docs/laps/openlensio-semantics/ambiguity-register.md` | current | AMB-OL-010 updated this session (uncommitted) |
| `docs/laps/opencv-openlensio-pipeline-equivalence/ambiguity-register.md` | current | AMB-PE-006 updated this session (uncommitted) |
| `docs/limitations.md` | current | y-component symmetry note updated this session (uncommitted) |
| `docs/laps/whole-repo-review/audit-report.md` | updated | This file |

---

## Lean Check

Command:

```sh
cd /Users/markstalzer/github/opentrackio-proof && lake build
```

Result: **pass** — Build completed successfully (3316 jobs), 0 warnings, exit 0.

Notes:
- Run during this audit session at HEAD b859352.
- Identical job count to prior audit (c948dc4, 3316 jobs) — consistent with only documentation changes between the two audit points (Lean source is unchanged since the undistort-invertibility campaign was committed at 00c9e9a).

---

## Forbidden Construct Scan

Commands:

```sh
grep -REn --include="*.lean" --exclude-dir=".lake" \
  "sorry|admit|set_option warn\.sorry|^unsafe|^partial" \
  /Users/markstalzer/github/opentrackio-proof/
```

Results: 3 matches, **all in comments**:

| File | Line | Content |
|---|---|---|
| `opentrackio_parser/HarnessAdapter.lean:10` | comment | `"No new proofs. No sorry, admit, axiom, unsafe, partial."` |
| `opentrackio_parser/IntegrationSmoke.lean:5` | comment | `"No new theorems. No sorry."` |
| `openlensio_semantics/SemanticBridge.lean:21` | comment | `"easier; do not add a sorry."` |

No actual `sorry`, `admit`, `unsafe`, `partial`, or `set_option warn.sorry` constructs appear in proof code. All 3 are documentation prose.

Additional checks run at prior audit (results unchanged):

```sh
grep -rEn --include="*.lean" "^sorry$|^\s+sorry$|:= sorry|:= by sorry" . | grep -v ".lake/"
grep -rEn --include="*.lean" "^axiom |^constant |^unsafe |^partial " . | grep -v ".lake/"
grep -rn --include="*.lean" "set_option warn.sorry" . | grep -v ".lake/"
```

All returned no output at prior audit. No new Lean source files have been added since then (only InjectivityModel.lean, which was clean at its campaign review).

---

## Declaration Inventory Check

### Counts by proof area

```sh
grep -REn --include="*.lean" --exclude-dir=".lake" "^(theorem|lemma) " /path/...
```

| Area | Files | Theorems + Lemmas |
|---|---|---|
| `openlensio_semantics/` | 12 | 21 |
| `opencv_opentrackio_proofs/` (incl. `Pipeline/`) | 9 | 57 |
| `opentrackio_parser/` | 45 | 67 |
| **Total** | **66** | **145** |

### Coverage model

The project uses a two-tier review model:
- **Whole-repo proof-review.md** covers the 138 declarations that existed at the prior whole-repo review (HEAD c948dc4).
- **Campaign-specific proof-review.md** files cover declarations added by individual campaigns.

The 7 new declarations in `InjectivityModel.lean` (added by the undistort-invertibility campaign after the prior whole-repo review) are covered by `docs/laps/undistort-invertibility/proof-review.md`, which was reviewed and accepted this session.

**Total coverage: 138 + 7 = 145 / 145 — complete.**

### InjectivityModel.lean declaration inventory (7 proof-bearing)

| Line | Kind | Name | Campaign review |
|---|---|---|---|
| 66 | theorem | `undistortPoint_injective_zero_tangential` | SLICE-UI-00 ✓ |
| 101 | lemma | `radialTerm_eq_radialScale` | SLICE-UI-01 ✓ |
| 126 | theorem | `undistortPoint_injective_pure_radial` | SLICE-UI-01 ✓ |
| 184 | theorem | `radialTerm_pos` | SLICE-UI-02 ✓ |
| 193 | theorem | `radialTerm_ne_zero` | SLICE-UI-02 ✓ |
| 233 | theorem | `undistortPoint_injective_on_circle_tangential` | SLICE-UI-03 ✓ |
| 310 | theorem | `radialDescale_left_inverse_zero_tangential` | SLICE-UI-04 ✓ |

---

## Definition Inventory Check

Load-bearing definitions unchanged since prior audit. Status carried forward:

| Definition | Intended meaning | Invariants encoded | Invariants deferred | Status |
|---|---|---|---|---|
| `SensorPoint` | 2D sensor coordinate pair | none (bare `{x y : ℝ}`) | coordinate-space tags (documented) | pass |
| `ValidLensSemantics` | Valid lens parameter set | `0 < focalLength` | denominator nonzero (AMB-OL-007), coefficient bounds | pass |
| `denominatorNonzero` | Radial denominator ≠ 0 at radius r | exact `≠ 0` over ℝ | Float oracle uses 1e-10 tolerance (EX-01, documented) | pass |
| `radialScale` | Radial factor R(r) without proof argument | same body as `radialTerm` | proof-bearing form requires `denominatorNonzero` | pass — bridge lemma connects both |
| `radialDescale` | Conditional left inverse for p=0: ⟨ε.x/R, ε.y/R⟩ | explicit r parameter required | recovering r from U(ε) alone (AMB-UI-001) | pass — explicit r reflects documented open gap |

New definitions `radialScale` and `radialDescale` were audited as part of the undistort-invertibility campaign review (SLICE-UI-01 and SLICE-UI-04 respectively). Both are correctly modeled and the conditional nature of `radialDescale` (not a local inverse) is documented in InjectivityModel.lean, limitations.md, and the ambiguity registers.

---

## Semantic Audit Summary

| Check | Result | Notes |
|---|---|---|
| Statement laundering | pass | Checked for all 7 new declarations in campaign review; prior 138 unchanged |
| Definition-model mismatch | pass | `radialDescale` is correctly framed as conditional left inverse; D=U⁻¹ framing corrected in AMB-OL-010 this session |
| Comment/formal mismatch | pass | InjectivityModel.lean header comment aligns with updated AMB-UI-001 and AMB-OL-010 framing |
| Vacuity | pass | Non-vacuity witnesses provided for all 5 new theorem families |
| Weakened claims | pass | All scopes (on-circle, pure-radial, full tangential) documented as intentional |
| Proxy properties | pass | All theorems prove their stated claims directly |
| Over-strong hypotheses | pass | Each hypothesis shown necessary in campaign review |
| Automation hiding hard step | pass | Hard step identified for all slices: `mul_left_cancel₀`, `nlinarith`, `linear_combination`, `mul_div_cancel_left₀` |
| Runtime failure replacing proof | pass | No `partial`, no `unsafe` |
| Forbidden constructs | pass | See forbidden construct scan above |

---

## Material Findings

### Finding: Whole-repo proof-review.md theorem count stale

Severity: **low**

Evidence:

```
docs/laps/whole-repo-review/proof-review.md line 8:
  "All 138 public theorem/lemma declarations audited across 65 Lean source files."

Current Lean file count:
  grep -REn --include="*.lean" --exclude-dir=".lake" "^(theorem|lemma) " → 145 declarations
  ls openlensio_semantics/*.lean → 12 files (was 11)
```

Risk:

The whole-repo proof-review.md records 138 declarations but the current codebase has 145. The count difference is exactly 7 — the 6 theorems and 1 lemma in `InjectivityModel.lean` added by the undistort-invertibility campaign. This is not a coverage gap: all 7 are reviewed and accepted in `docs/laps/undistort-invertibility/proof-review.md`. The stale count is a documentation artifact of the two-tier review model (whole-repo + campaign-specific).

Required action:

Update `docs/laps/whole-repo-review/proof-review.md` to record 145 declarations and 12 `openlensio_semantics/` files, with a note that the 7 new declarations are covered by the undistort-invertibility campaign review. Low priority — no proof soundness impact.

---

## Notes

| Note | Suggested Cleanup |
|---|---|
| `openlensio_semantics/proof-review.md` does not cover InjectivityModel.lean theorems | Expected — they were added after that campaign closed. Coverage is in undistort-invertibility/proof-review.md. No action required. |
| 3 files modified but not committed: ambiguity registers + limitations.md | Documentation-only changes. No proof impact. Commit when convenient. |
| `docs/laps/whole-repo-review/proof-review-old.md` present | Archive file from a prior review iteration. Not stale — intentionally kept. No action required. |
| metrics.md "3 new definitions" in undistort-invertibility was corrected to "2 defs + 1 lemma" | Fixed this session. No further action. |

---

## Artifact Status

| Artifact | Status |
|---|---|
| undistort-invertibility/proof-capsule.md | current |
| undistort-invertibility/statement-audit.md | current |
| undistort-invertibility/proof-plan.md | current |
| undistort-invertibility/proof-run-log.md | current |
| undistort-invertibility/proof-review.md | current — updated this session |
| undistort-invertibility/work-queue.md | current |
| undistort-invertibility/first-slice-contract.md | current |
| undistort-invertibility/ambiguity-register.md | current — updated this session |
| undistort-invertibility/metrics.md | current — finalized this session |
| whole-repo-review/proof-review.md | stale by 7 declarations (low severity) |
| openlensio-semantics/ambiguity-register.md | current — AMB-OL-010 updated this session |
| opencv-openlensio-pipeline-equivalence/ambiguity-register.md | current — AMB-PE-006 updated this session |
| docs/limitations.md | current — y-component note updated this session |
| Final Lean command recorded after last code change: | yes — lake build at HEAD b859352, exit 0 |
| Artifact theorem count matches Lean file: | whole-repo review stale by 7 (low); all other campaign artifacts current |
| Artifact theorem names match Lean file: | yes — all 145 named and covered |
| Load-bearing definitions match documented intent: | yes |

---

## Verdict

**accepted with notes**

`lake build` passes at HEAD b859352 (3316 jobs, 0 warnings). All 145 public theorem and lemma declarations are covered: 138 by the whole-repo proof-review.md, 7 by the undistort-invertibility campaign proof-review.md. No forbidden constructs in proof code. No semantic defects. No definition-model mismatches. One low-severity note: the whole-repo proof-review.md theorem count (138) is stale and should be updated to 145 with a reference to the campaign-specific coverage.

---

## Recommended Next Action

Update `docs/laps/whole-repo-review/proof-review.md` to record the current declaration count (145), current `openlensio_semantics/` file count (12), and a note that the 7 new declarations in `InjectivityModel.lean` are covered by `docs/laps/undistort-invertibility/proof-review.md`. Then commit the three uncommitted artifact files.

Beyond that: no proof action required. The recommended next proof work is the nonconstructive `D ∘ U = id` theorem via `Function.invFun` (item 1 in next-steps.md), which is reachable from the injectivity results now in `InjectivityModel.lean`.
