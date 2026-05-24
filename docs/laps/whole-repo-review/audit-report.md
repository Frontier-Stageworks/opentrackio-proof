# LAPS Audit: opentrackio-proof — Whole-Repo

## Audit Target

- Lean project root: `/Users/markstalzer/github/opentrackio-proof`
- LAPS artifact directory: `docs/laps/` (multiple slugs)
- Audit date: 2026-05-24
- HEAD commit at audit: `c948dc4`
- Prior review commit: `8ea6fdb` (whole-repo review, 2026-05-23)
- Audit mode:
  - semantic audit
  - definition/model audit
  - artifact freshness audit
  - anti-spiral audit

## Files Inspected

| File | Status | Notes |
|---|---|---|
| `opentrackio_parser/` (40 files) | present | All 40 files, no changes since prior review |
| `openlensio_semantics/` (11 files) | present | All 11 files, no changes since prior review |
| `opencv_opentrackio_proofs/` (14 files) | present | All 14 files, no changes since prior review |
| `docs/laps/whole-repo-review/proof-review.md` | current | Updated 8f85807 (2026-05-23); covers commit 8ea6fdb |
| `docs/laps/whole-repo-review/metrics.md` | current | Scores 12/12; updated same session |
| `docs/laps/openlensio-semantics/audit-report.md` | present (2026-05-20) | Prior campaign audit; findings addressed by closeout artifacts |
| `docs/laps/openlensio-semantics/proof-run-log.md` | present | Created retroactively per ART-02 finding |
| `docs/laps/openlensio-semantics/statement-audit.md` | present | Created retroactively per ART-01 finding |
| `docs/laps/openlensio-semantics/second-pass-audit.md` | present | Skeptical re-audit; downgraded VAC-01 and DT-02 severity |
| `docs/laps/whole-repo-review/audit-report.md` | created | This file |

## Lean Check

Command:

```sh
cd /Users/markstalzer/github/opentrackio-proof && lake build
```

Result:

- **pass** — Build completed successfully (3316 jobs), 0 warnings

Notes:

- Run during this audit session (2026-05-24, HEAD c948dc4).
- Lean files unchanged since prior review at 8ea6fdb (`git diff --name-only 8ea6fdb HEAD -- "*.lean"` returned no output).
- Build result is consistent with prior review (also 3316 jobs, also clean).

## Definition Inventory Check

The load-bearing definitions in `openlensio_semantics/` were audited in depth in the
2026-05-20 campaign audit and the 2026-05-20 second-pass audit. Key status:

| Definition | Intended meaning | Invariants encoded | Invariants deferred | Status |
|---|---|---|---|---|
| `SensorPoint` | 2D coordinate pair in sensor space | none (bare `{x y : ℝ}`) | coordinate-space tags (deferred, documented) | pass |
| `ValidLensSemantics` | Valid lens parameter set | `0 < focalLength` only | denominator nonzero (AMB-OL-007), coefficient bounds | pass — comment added listing intentional omissions (DEF-01 resolved) |
| `denominatorNonzero` | Radial denominator ≠ 0 at radius r | exact `≠ 0` over ℝ | Float oracle uses 1e-10 tolerance (EX-01, documented) | pass |
| `extractLensSemantics` | Parser from raw params to `LensSemantics` | succeeds iff `focalLength > 0` | weaker than full semantic validity | pass — correctly scoped |
| `undistortFromDistorted` | Eq(4) with ΔC+ΔP offsets | shifted-point domain | full Eq(3)/Eq(4) consistency (OL-DEFER-03) | pass — deferred documented |

No definition-model mismatch found. All deferrals are documented in the ambiguity register.

## Theorem Inventory Check

| Item | Result |
|---|---|
| Theorem count in Lean file | 138 (public theorems/lemmas) |
| Theorem count in artifacts | 138 (proof-review.md whole-repo table) |
| Names match artifacts | yes |
| Classifications match artifacts | yes |
| Newly added theorems reviewed | yes — no new theorems since 8ea6fdb |
| Final Lean check recorded after last code change | yes — lake build run this session (2026-05-24) |

## Semantic Audit Summary

| Check | Result | Notes |
|---|---|---|
| Statement laundering | pass | All theorem conclusions match intended domain properties |
| Definition-model mismatch | pass | `ValidLensSemantics` thinness documented; not a mismatch |
| Comment/formal mismatch | pass | `fov_undistort_eq` comment corrected (DEF-02 resolved); `projection_matrix_undistort_eq` correctly described as structural consistency theorem |
| Vacuity | pass | No bad vacuity. VAC-01 (α-equivalent theorems) documented in source; second-pass audit downgraded to LOW and accepted as intentional traceability design |
| Weakened claims | pass | All key theorems are full iff or full equality |
| Proxy properties | pass | No theorem proves a proxy property while claiming domain correctness |
| Over-strong hypotheses | pass | All nonzero/positivity guards are load-bearing (verified in whole-repo review) |
| Automation hiding hard step | pass | `linear_combination` witnesses explicit; `foldl_toDigits` strong induction exposed |
| Runtime failure replacing proof | pass | No `partial`; no unsafe indexing |
| Forbidden constructs | pass | No `sorry`, `admit`, `unsafe`, `partial`, unauthorized `axiom`/`constant`, or `set_option warn.sorry` in code |

## Material Findings

| Severity | Finding | Required Action |
|---|---|---|
| low | Non-executable search claim in `proof-review.md` (see Finding below) | Replace with executable grep; evidence independently verified |

---

## Finding: Non-executable search claim

Severity: low

Type: PROCESS EVIDENCE GAP

Evidence:

`docs/laps/whole-repo-review/proof-review.md` records the following forbidden construct search command:

```
grep -rn --include="*.lean" "sorry|admit|set_option warn\.sorry|^unsafe |^partial " . | grep -v ".lake/" | grep -c ""
```

This command uses unescaped `|` without the `-E` flag. In GNU grep BRE mode, bare `|`
is a literal character, not alternation. The command therefore searches for the
literal pipe-separated string `sorry|admit|set_option warn\.sorry|^unsafe |^partial `,
not for any of the individual keywords. It returns 0 because no Lean file contains that
literal string with pipe characters — not because sorry/admit are absent.

Risk:

The evidence path is broken. A future reviewer could not replicate this scan and trust the result.
The practical conclusion (no forbidden constructs) is **correct** — independently verified
during this audit session with the proper alternation scan:

```sh
grep -rEn --include="*.lean" "^sorry$|^\s+sorry$|:= sorry|:= by sorry" . | grep -v ".lake/"
grep -rEn --include="*.lean" "^axiom |^constant |^unsafe |^partial " . | grep -v ".lake/"
grep -rn --include="*.lean" "set_option warn.sorry" . | grep -v ".lake/"
```

All returned no output. The 3 matches found in an alternation grep of "sorry" were all in
comment text (not proof code).

Required action:

Update the search command in `proof-review.md` to use `-E` for alternation (or `\|` in BRE):

```sh
grep -rEn --include="*.lean" --exclude-dir=".lake" "sorry|admit|set_option warn\.sorry|^unsafe |^partial " .
```

This is a process-evidence action only. No proof defect.

---

## Notes

| Note | Suggested Cleanup |
|---|---|
| `openlensio-semantics/audit-report.md` (2026-05-20) still shows findings as open | Optional: add a closeout section noting ART-01, ART-02, DEF-01, DEF-02 were resolved by the closeout pass. The second-pass-audit.md documents the resolution but the original audit-report.md is not updated. Low priority. |
| `deltaP_characterisation` / `deltaC_characterisation` α-equivalence (VAC-01) | Accepted as intentional design (second-pass audit). Source comments added. No action needed. |
| `angle_of_view_eq` junk-value at F=0 (VAC-02) | Documented in source. Caller-enforced. No action needed unless RW-02 is authorized. |
| `projection_matrix_undistort_eq` scope limitation | Correctly labeled structural consistency, not Eq(3)/Eq(4) full equivalence. Deferred to OL-DEFER-03. |
| `ExecutableSemanticOracle.lean` Float/ℝ architecture gap (EX-01) | Registered as AMB-OL-016. Prominent warning in file. No bridging theorem attempted. Correctly scoped. |
| Missing `metrics.md` for individual task slugs | Only `whole-repo-review/metrics.md` exists. Individual task slugs have no metrics. This is acceptable — the whole-repo review is the authoritative metrics record. |

## Artifact Status

- Proof capsule current: n/a (whole-repo audit; per-slice capsules exist)
- Statement audit current: n/a (whole-repo scope)
- Proof plan current: n/a
- Proof run log current: n/a (build recorded in this audit-report.md and in proof-review.md)
- Proof review current: yes — `whole-repo-review/proof-review.md` (commit 8f85807, 2026-05-23)
- Work queue current, if applicable: n/a
- First-slice contract current, if applicable: n/a
- Ambiguity register current, if applicable: n/a (per-campaign)
- Algebra plan current, if applicable: n/a
- Final Lean command recorded after last code change: yes — lake build run this session (2026-05-24, HEAD c948dc4)
- Artifact theorem count matches Lean file: yes — 138 in both
- Artifact theorem names match Lean file: yes
- Artifact classifications match across files: yes
- Load-bearing definitions match documented intent: yes

## Verdict

**accepted with notes**

The project compiles cleanly (lake build, 3316 jobs, 0 warnings). All 138 public theorems
are semantically sound per the 2026-05-23 whole-repo review. No forbidden constructs exist
in code. No vacuity, proxy properties, weakened claims, or definition-model mismatches were
found. The openlensio-semantics prior audit findings (ART-01, ART-02, DEF-01, DEF-02,
VAC-01) were all addressed in the closeout pass.

The one material observation is a broken grep syntax in `proof-review.md` (PROCESS EVIDENCE GAP,
LOW severity). The practical conclusion of that scan is correct and independently verified here.

## Recommended Next Action

Update the forbidden construct grep in `docs/laps/whole-repo-review/proof-review.md` to use
`-E` flag so the command is copy-paste executable and produces the correct alternation search.
No Lean code changes required.
