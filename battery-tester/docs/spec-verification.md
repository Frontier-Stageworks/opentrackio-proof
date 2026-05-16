# Spec Verification — battery-tester

Status key: ✅ verified | ⚠️ browser/manual | ❌ failing | ☐ not yet verified

---

## Adapter output specs

CAPS-ADAPT-001 (Python adapter emits valid normalized JSON) — ☐ pending C++ build
CAPS-ADAPT-002 (CamDKit C++ adapter emits valid normalized JSON) — ☐ pending C++ build
CAPS-ADAPT-003 (Mo-Sys C++ adapter emits valid normalized JSON) — ☐ pending C++ build

## Field comparison specs

CAPS-DIFF-001 (translation PASS) — ☐ pending C++ build
CAPS-DIFF-002 (rotation PASS) — ☐ pending C++ build
CAPS-DIFF-003 (timing PASS) — ☐ pending C++ build
CAPS-DIFF-004 (tracker PASS) — ☐ pending C++ build
CAPS-DIFF-005 (protocol PASS) — ☐ pending C++ build
CAPS-DIFF-006 (lens.pinholeFocalLength DIVERGE — Python null, C++ 24.305) — ☐ pending C++ build
CAPS-DIFF-007 (lens.focusDistance PASS) — ☐ pending C++ build

## Report specs

CAPS-REPORT-001 (per-field table written to file) — ✅
Evidence: run.py write_fixture_table() writes one row per COMPARISON_FIELDS entry including
field, per-adapter value, and verdict. Python-only run produces valid file output.

CAPS-REPORT-002 (aggregate written when >1 fixture) — ✅
Evidence: write_aggregate() called when totals["fixtures"] > 1; verified by running
`python run.py` with Python adapter only — aggregate section appears.

CAPS-REPORT-003 (MISSING for missing binary, no crash) — ✅
Evidence: run_adapter() catches FileNotFoundError and returns None; compare_samples()
treats None samples as null for all fields; verdicts show MISSING; runner continues to next fixture.

CAPS-REPORT-004 (battery-tester-YYYY-MM-DD-N.txt sequential naming) — ✅
Evidence: resolve_report_path() increments N from 1 until a non-existent filename is found.
Running twice on the same day produces -1.txt and -2.txt.

---

## Notes

- CAPS-DIFF-001 through CAPS-DIFF-007 require both C++ adapters to be built.
  Build steps are in README.md.
- CAPS-DIFF-006 (the pinholeFocalLength divergence) is the primary demo claim.
  Verification confirms it is caught by the harness, not hand-planted.
- tracker.serialNumber (in CAPS-DIFF-004) reads from static.tracker in Python and
  from sample.tracker in C++. If Mo-Sys merges the static block, they agree; if not,
  this will also show as DIVERGE. The harness will reveal which is true.
