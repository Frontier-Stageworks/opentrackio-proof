# Demo Script — battery-tester

## Demo Goal
Prove that a field-by-field differential harness catches real divergences between the Python and C++ OpenTrackIO parser implementations on identical input.

## Before You Start

- **Setup:** Build the Mo-Sys C++ adapter (see README.md — one `cmake --build` command)
- **Python deps:** `pip install cbor2 jsonschema` in your Python environment
- **Starting state:** Clean terminal, `battery-tester/` as working directory, no `battery-tester-*.txt` files present
- **Reset:** Delete any `battery-tester-*.txt` files to restart the sequential numbering

---

## Demo Steps

### Step 1 — Single fixture run

**Action**
```
python run.py --fixture complete_static_example
```

**Expected Visible Outcome**
Terminal prints: `Writing report to: battery-tester-YYYY-MM-DD-1.txt` then `Done. 17 pass, 1 diverge, 0 missing across 1 fixture(s).`
The file appears in the working directory.

**What the Audience Should Notice**
Open the file. A column-aligned table appears with 18 rows — one per field. The `python` and `cpp-mosys` columns are visible side by side.

**What This Proves**
Both adapters ran, parsed the same canonical fixture, and produced comparable output across 17 of 18 fields.

**Failure Signal**
File not created, or terminal shows all MISSING (means the C++ binary was not found — check build step).

---

### Step 2 — Point to the divergence

**Action**
Scroll to the `lens.pinholeFocalLength` row in the open report file (already visible from Step 1).

**Expected Visible Outcome**
```
lens.pinholeFocalLength    null    24.305    DIVERGE
```

**What the Audience Should Notice**
Python returns `null`; the C++ adapter returns `24.305`. The `DIVERGE` verdict is the signal.

**What This Proves**
The Python parser's `get_focal_length()` reads the key `lens.focalLength`, which does not exist in the v1.0.1 schema. The correct key is `lens.pinholeFocalLength`. This is a real defect in `opentrackio_lib.py` — caught automatically by comparing two parsers on identical input.

**Failure Signal**
Row shows `PASS` (Python accidentally found a value) or the row is absent entirely.

---

### Step 3 — All fixtures, aggregate

**Action**
```
python run.py
```

**Expected Visible Outcome**
Terminal prints: `Writing report to: battery-tester-YYYY-MM-DD-2.txt` then `Done. N pass, 4 diverge, M missing across 4 fixture(s).`

**What the Audience Should Notice**
Open the second report file. Four fixture tables appear, followed by an AGGREGATE section. The `lens.pinholeFocalLength` divergence appears in each fixture that contains that field, accumulating in the DIVERGE count. MISSING entries are expected — the "recommended" fixtures intentionally omit many fields.

**What This Proves**
The bug propagates consistently across the full fixture suite. MISSING is not a bug — it reflects the intended minimal coverage of the recommended fixture set.

**Failure Signal**
Aggregate counts don't sum to total fields tested, or a fixture table is missing entirely.

---

## Reset / Recovery

Delete any `battery-tester-*.txt` files to reset sequential numbering. No other state to clear.

## Demo Completion Criteria

- Flow 1: full comparison table shown for `complete_static_example` ✓
- Flow 2: `lens.pinholeFocalLength` DIVERGE row visible and explained ✓
- Flow 3: aggregate counts shown across all 4 fixtures ✓
