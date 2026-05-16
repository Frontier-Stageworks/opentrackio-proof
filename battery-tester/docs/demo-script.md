# Demo Script — battery-tester

## Demo Goal
Prove that a field-by-field differential harness catches real divergences between the Python and C++ OpenTrackIO parser implementations on identical input.

## Before You Start

- **Working directory:** `battery-tester/` — all commands run from here
- **Setup:** Build the Mo-Sys C++ adapter (see README.md — one `cmake --build` command). The binary must exist at `../opentrackio-cpp/build/tools/dump_sample/dump_sample`.
- **Python deps:** `pip install cbor2 jsonschema` in your Python environment
- **Starting state:** No `battery-tester-*.txt` files in the directory. Delete any that exist before starting — they affect the sequential file numbering.

---

## Demo Steps

### Step 1 — Run the harness on a single fixture

**Action**
```
python run.py --fixture complete_static_example
```

**What Happens**
The harness invokes two adapters — the Python parser (`opentrackio_lib.py` from camdkit) and the Mo-Sys C++ binary (`dump_sample`) — against the same JSON fixture file (`fixtures/complete_static_example.json`). Each adapter reads the fixture independently and emits a normalized flat JSON object. The harness compares those outputs field by field.

**Expected Terminal Output**
```
Writing report to: battery-tester-2026-05-16-1.txt
Done. 17 pass, 1 diverge, 0 missing across 1 fixture(s).
Report: battery-tester-2026-05-16-1.txt
```

**Open the report file.** It contains a column-aligned table with 18 rows — one per comparison field. The columns are `FIELD`, `python`, `cpp-mosys`, and `VERDICT`.

Each row shows:
- The field path (e.g. `timing.sampleRate`, `transforms.Camera.translation.x`)
- The value each adapter extracted from the fixture
- A verdict: `PASS` if they agree within tolerance, `DIVERGE` if they disagree, `MISSING` if both returned null

**What This Proves**
Both adapters ran against identical input and agreed on 17 of 18 fields. The harness is working.

**Failure Signal**
File not created → Python error (check working directory and deps). All rows show `MISSING` → the C++ binary was not found (check the build step in README.md).

---

### Step 2 — Identify the divergence

**Action**
In the open report file, find the `lens.pinholeFocalLength` row. It is near the bottom of the table.

**Expected Row**
```
lens.pinholeFocalLength                     null                24.305              DIVERGE
```

**What to Explain**
The Python adapter returns `null` for this field. The C++ adapter returns `24.305`. The fixture contains the value — the C++ adapter reads it correctly. The Python parser's `get_focal_length()` method reads the key `lens.focalLength`, which does not exist in the v1.0.1 schema. The correct key is `lens.pinholeFocalLength`. Because the key lookup silently fails, Python returns `None` rather than raising an error — the bug is invisible without a comparison.

This defect was found automatically by running both parsers on the same input. A fix has been submitted upstream: [SMPTE/ris-osvp-metadata-camdkit#210](https://github.com/SMPTE/ris-osvp-metadata-camdkit/pull/210). Once merged, this row will show `PASS`.

**Failure Signal**
Row shows `PASS` — Python unexpectedly returned a value. Row is absent entirely — field was removed from the comparison list.

---

### Step 3 — Run all fixtures and check the aggregate

**Action**
```
python run.py
```

**What Happens**
The harness runs both adapters against all four fixtures:
- `complete_static_example` — full static metadata
- `complete_dynamic_example` — full dynamic metadata (per-frame transforms, timing)
- `recommended_static_example` — minimal static metadata (many fields intentionally absent)
- `recommended_dynamic_example` — minimal dynamic metadata

**Expected Terminal Output**
```
Writing report to: battery-tester-2026-05-16-2.txt
Done. 55 pass, 4 diverge, 13 missing across 4 fixture(s).
Report: battery-tester-2026-05-16-2.txt
```

**Open the second report file.** It contains four fixture tables followed by an `AGGREGATE` section. Look for:

1. **`lens.pinholeFocalLength` appears as `DIVERGE` in each "complete" fixture** — the bug is consistent, not a one-off.
2. **`lens.pinholeFocalLength` appears as `MISSING` in the "recommended" fixtures** — those fixtures omit the field entirely, so neither adapter has a value. `MISSING` is expected here, not a bug.
3. **The `AGGREGATE` section** tallies totals across all fixtures: `55 pass, 4 diverge, 13 missing`. The 13 `MISSING` entries come from fields the "recommended" fixtures deliberately omit.

**What This Proves**
The divergence is consistent across every fixture that contains `lens.pinholeFocalLength`. `MISSING` reflects intentional fixture coverage choices, not additional parser bugs.

**Failure Signal**
Aggregate counts don't add up to `fixtures × 18 fields`. A fixture table is absent. The diverge count is higher than 4 (a new disagreement appeared).

---

## Reset / Recovery

Delete any `battery-tester-*.txt` files to reset sequential numbering. No other state to clear.

## Demo Completion Criteria

- Step 1: report file created, 18-row comparison table visible, `17 pass 1 diverge` summary shown ✓
- Step 2: `lens.pinholeFocalLength` DIVERGE row located, root cause explained, upstream PR referenced ✓
- Step 3: all-fixture aggregate shown, `MISSING` vs `DIVERGE` distinction explained ✓
