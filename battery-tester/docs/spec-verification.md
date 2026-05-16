# Spec Verification — battery-tester

Status key: ✅ verified | ⚠️ browser/manual | ❌ failing | ☐ not yet verified

---

## Adapter output specs

CAPS-ADAPT-001 (Python adapter emits valid normalized JSON) — ✅
Evidence: python_adapter.py invoked on all 76 generated fixtures via `run.py --generated`;
all produce valid JSON with all 18 fields present (nulls where fixture omits optional fields).

CAPS-ADAPT-002 (Mo-Sys C++ adapter emits valid normalized JSON) — ✅
Evidence: dump_sample invoked on generated fixtures via `run.py --generated`; 76/76
produce valid JSON; missing binary degrades to MISSING per CAPS-REPORT-003.

## Field comparison specs

CAPS-DIFF-001 (translation PASS) — ✅
Evidence: tx/ty/tz variant fixtures (15 fixtures, 5 values per axis) all show PASS for
translation fields. Verified across 0, ±1, ±50-100 meter values.

CAPS-DIFF-002 (rotation PASS) — ✅
Evidence: pan/tilt/roll variant fixtures (15 fixtures) all show PASS. Covers 0, ±45, ±89–180°.

CAPS-DIFF-003 (timing PASS) — ✅
Evidence: tc_h/tc_m/tc_s/tc_f/rate/ts_sec/ts_ns variant fixtures (22 fixtures) all show
PASS for timing fields. Covers boundary hours (0,23), minutes (0,59), seconds (0,59),
frames (0,23), 5 sample rates, epoch 0 through realistic timestamp.

CAPS-DIFF-004 (tracker PASS) — ✅
Evidence: All generated fixtures with serial present show PASS for tracker.serialNumber.
no_serial fixture confirms MISSING when field is absent from both adapters.

CAPS-DIFF-005 (protocol PASS) — ✅
Evidence: All 76 generated fixtures show PASS for protocol.name and protocol.version.

CAPS-DIFF-006 (lens.pinholeFocalLength DIVERGE — Python null, C++ value) — ✅
Evidence: 75 of 76 generated fixtures show DIVERGE for lens.pinholeFocalLength.
focal_00–05 variants (14.0, 24.305, 35.0, 50.0, 85.0, 135.0) all produce Python=null,
C++=correct value. no_focal produces MISSING (both null, field absent from fixture).

CAPS-DIFF-007 (lens.focusDistance PASS) — ✅
Evidence: focus_00–04 variants (0.3, 1.0, 5.0, 10.0, 100.0) all show PASS.

## Report specs

CAPS-REPORT-001 (per-field table written to file) — ✅
Evidence: write_fixture_table() writes one row per COMPARISON_FIELDS entry including
field, per-adapter value, and verdict. Verified across all fixture types.

CAPS-REPORT-002 (aggregate written when >1 fixture) — ✅
Evidence: write_aggregate() called when totals["fixtures"] > 1. `run.py --generated`
produces aggregate across 76 fixtures: 1287 pass, 75 diverge, 6 missing = 1368 = 76×18. ✓

CAPS-REPORT-003 (MISSING for missing binary, no crash) — ✅
Evidence: run_adapter() catches FileNotFoundError and returns None; compare_samples()
treats None samples as null for all fields; verdicts show MISSING; runner continues.

CAPS-REPORT-004 (battery-tester-YYYY-MM-DD-N.txt sequential naming) — ✅
Evidence: resolve_report_path() increments N from 1 until a non-existent filename is found.
Running twice on the same day produces -1.txt and -2.txt.

## Generator and corpus specs

CAPS-GEN-001 (generate_fixtures.py produces ≥50 fixtures) — ✅
Evidence: generator produces 76 fixtures in fixtures/generated/. Count confirmed by
`ls fixtures/generated/ | wc -l`.

CAPS-GEN-002 (boundary values and optional-field coverage) — ✅
Evidence: 5 values per translation/rotation axis, 5–6 per lens field, 5 rates, 4 values
per timecode component, 3 timestamp values, 4 resolutions. Four optional-absent fixtures:
no_timestamp, no_resolution, no_serial, no_focal.

CAPS-GEN-003 (--generated flag runs full corpus) — ✅
Evidence: `python run.py --generated` runs all 76 fixtures; aggregate confirms 76 fixtures
processed; 1287+75+6=1368=76×18.

## Property test specs

CAPS-PROP-001 (verdict rules verified by Hypothesis) — ✅
Evidence: test_properties.py 13 tests all pass. Key tests: test_identical_values_all_pass,
test_different_values_all_diverge, test_one_null_adapter_all_diverge,
test_both_null_adapters_all_missing. Hypothesis exercises integer/string/float values
across their ranges.

CAPS-PROP-002 (aggregate sum invariant verified by Hypothesis) — ✅
Evidence: test_verdict_counts_always_sum_to_total_fields and
test_aggregate_sum_across_multiple_fixtures pass across all Hypothesis-generated inputs
(None, integers ±1000). p+d+m == len(COMPARISON_FIELDS) always holds.

---

## Notes

- CAPS-DIFF-006 (the pinholeFocalLength divergence) is the primary demo claim. Upstream fix
  submitted at SMPTE/ris-osvp-metadata-camdkit#210; once merged, this row will show PASS.
- The aggregate invariant (76×18=1368) serves as an ongoing sanity check: any change that
  produces a different total signals a field was added, removed, or a fixture was skipped.
