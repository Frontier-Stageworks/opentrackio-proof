# Demo Script — battery-tester

## Demo Goal
Prove that a field-by-field differential harness catches real divergences between Python and C++ OpenTrackIO parser implementations on identical input.

## Before You Start

- **Setup:** Build both C++ adapters (see README.md — two `cmake --build` commands)
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
Terminal prints: `Writing report to: battery-tester-2026-05-16-1.txt` then `Done. N pass, M diverge, 0 missing across 1 fixture(s).`
The file `battery-tester-2026-05-16-1.txt` appears in the working directory.

**What the Audience Should Notice**
Open the file. A column-aligned table appears with ~18 rows — one per field. The `python`, `cpp-camdkit`, and `cpp-mosys` columns are visible side by side.

**What This Proves**
All three adapters ran, parsed the same canonical fixture, and produced comparable output. The harness infrastructure works end-to-end.

**Failure Signal**
File not created, or terminal shows `0 pass, 0 diverge` with all MISSING (means C++ binaries not found — check build step).

---

### Step 2 — Point to the divergence

**Action**
Scroll to the `lens.pinholeFocalLength` row in the open report file (no new command needed).

**Expected Visible Outcome**
The row shows: `lens.pinholeFocalLength | null | 24.305 | 24.305 | DIVERGE`

**What the Audience Should Notice**
Python returns `null`; both C++ adapters return `24.305`. The `DIVERGE` verdict in the final column is the signal.

**What This Proves**
The Python parser's `get_focal_length()` reads the key `lens.focalLength`, which does not exist in the current schema. The correct key is `lens.pinholeFocalLength`. This is a real defect in `opentrackio_lib.py` — and the harness caught it automatically by comparing parsers on identical input.

**Failure Signal**
Row shows `PASS` (Python accidentally found a value) or the row is absent entirely.

---

### Step 3 — All fixtures, aggregate

**Action**
```
python run.py
```

**Expected Visible Outcome**
Terminal prints: `Writing report to: battery-tester-2026-05-16-2.txt` then `Done. N pass, M diverge, 0 missing across 4 fixture(s).`

**What the Audience Should Notice**
Open `battery-tester-2026-05-16-2.txt`. Four fixture tables appear, followed by an AGGREGATE section. The `lens.pinholeFocalLength` divergence appears in each fixture that includes that field, accumulating in the DIVERGE count.

**What This Proves**
The harness scales across the full canonical fixture suite. The single key-name bug in the Python parser surfaces consistently across every fixture that contains `lens.pinholeFocalLength`.

**Failure Signal**
Aggregate counts don't sum to total fields tested, or a fixture table is missing entirely.

---

## Reset / Recovery

Delete any `battery-tester-*.txt` files to reset sequential numbering. No other state to clear — each run is fully independent.

## Demo Completion Criteria

- Flow 1: full comparison table shown for `complete_static_example` ✓
- Flow 2: `lens.pinholeFocalLength` DIVERGE row visible and explained ✓
- Flow 3: aggregate counts shown across all 4 fixtures ✓
