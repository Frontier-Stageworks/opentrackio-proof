# Slice 18 — Lean Adapter for battery-tester
# battery-tester-lean-adapter

**Status:** COMPLETE
**Date:** 2026-05-19

---

## Goal

Integrate the proof-backed Lean OpenTrackIO model into `battery-tester` as an
optional third oracle adapter alongside Python and C++.

---

## Architecture

```
JSON fixture
  ├─ Python adapter      (opentrackio_lib from camdkit)
  ├─ C++ adapter         (dump_sample binary, optional)
  └─ Lean adapter        (proof-backed AST oracle, optional via --with-lean)
       ↓
  field-by-field comparator  →  dated text report
```

---

## How to run

```bash
# Lean adapter included
python run.py --fixture complete_static_example --with-lean

# All canonical fixtures, three-way comparison
python run.py --with-lean

# Generated corpus
python run.py --generated --with-lean

# Existing two-adapter mode (unchanged)
python run.py --fixture complete_static_example
python run.py
python run.py --generated
```

---

## Files

| File | Role |
|---|---|
| `opentrackio_parser/HarnessAdapter.lean` | Lean module: extracts 18 fields from `decodeSample`, emits TSV |
| `battery-tester/adapters/lean_adapter.py` | Python wrapper: converts fixture JSON → Lean literal, runs `lake env lean --run`, parses TSV output |
| `battery-tester/run.py` | Runner: `--with-lean` flag, conditionally appends Lean to the adapter list |

---

## Lean adapter architecture

### Boundaries

- **Python** parses fixture JSON bytes (`json.load`). Lean does not see raw bytes.
- **Python** converts the parsed Python JSON value into a Lean `JsonValue` AST literal.
- **Lean** operates exclusively on the `JsonValue` AST — proof semantics are applied
  at the AST level.
- Lean does **not** verify byte-level JSON parsing.
- Byte-level numeric spelling preservation is **not** guaranteed: `json.load` may alter
  the original spelling (e.g., `1.0` vs `1`).

### Execution path

```
lean_adapter.py
  1. json.load(fixture_path)           # Python parses JSON bytes
  2. _py_to_lean(data)                 # Convert to Lean JsonValue literal
  3. Write temp runner.lean:
       import HarnessAdapter
       def fixture : JsonValue := <literal>
       def main : IO Unit :=
         IO.println (renderComparisonFields fixture)
  4. lake env lean --run <runner.lean> # Run under Lake environment
  5. Parse TSV output → dict           # Type-coerce fields
  6. json.dumps(out)                   # Emit JSON to stdout
```

**Native `lake exe` is not used.** `lake env lean --run` is the required path.

### Python JSON → Lean JsonValue mapping

| Python type | Lean constructor |
|---|---|
| `None` | `.null` |
| `True` | `.bool true` |
| `False` | `.bool false` |
| `str` | `.string "..."` (backslash-escaped) |
| `int` | `.number "<n>"` |
| `float` | `.number "<repr(x)>"` |
| `list` | `.array [...]` |
| `dict` | `.object [(key, val), ...]` |

Object insertion order is preserved. Numeric literal spelling uses Python's `repr()`
for floats (shortest round-trip representation) and `str()` for integers.

### HarnessAdapter.lean

`renderComparisonFields (j : JsonValue) : String` calls `decodeSample j`.

- On decode failure: all 18 fields emitted as `"null"`.
- On decode success: each field extracted from the `Sample` struct, rendered as a
  string, or `"null"` if absent.

`PositiveRational` fields are rendered as `"num/den"` (e.g., `"24/1"`, `"24000/1001"`).
The Python adapter converts these to `float` via integer division before comparison.

`SensorResolution.width` and `.height` are `Nat` in the model; rendered via `toString`.

### Key semantic claim

Lean reads `lens.pinholeFocalLength` via the normative decoder key.
Lean never reads `lens.focalLength` as a synonym.

If `lens.pinholeFocalLength` is absent in the JSON, Lean reports `null`.
If `lens.focalLength` is present but `lens.pinholeFocalLength` is absent,
Lean still reports `null` — the wrong key is invisible to the decoder.

This is the precise bug that surfaces as DIVERGE in the report:

```
lens.pinholeFocalLength    null    24.305    24.305    DIVERGE
```

Python reads the wrong key (`focalLength`) and returns `null`.
C++ and Lean agree on the normative value.

---

## Comparison fields

All 18 battery-tester fields are covered by the Lean adapter:

| Field | Lean model path |
|---|---|
| `protocol.name` | `s.protocol.name` |
| `protocol.version` | `s.protocol.version` → `"M.m.p"` |
| `tracker.slate` | `s.tracker.slate.val` |
| `tracker.serialNumber` | `s.static.tracker.serialNumber.val` |
| `timing.timecode` | `s.timing.timecode` → `"HH:MM:SS:FF"` |
| `timing.sampleTimestamp.seconds` | `s.timing.sampleTimestamp.seconds` |
| `timing.sampleTimestamp.nanoseconds` | `s.timing.sampleTimestamp.nanoseconds` |
| `timing.sampleRate` | `s.timing.sampleRate` → `"num/den"` |
| `camera.activeSensorResolution.width` | `s.static.camera.activeSensorResolution.width` |
| `camera.activeSensorResolution.height` | `s.static.camera.activeSensorResolution.height` |
| `transforms.Camera.translation.x/y/z` | first transform with `id = "Camera"` |
| `transforms.Camera.rotation.pan/tilt/roll` | same transform |
| `lens.focusDistance` | `s.lens.focusDistance` |
| `lens.pinholeFocalLength` | `s.lens.pinholeFocalLength` |

---

## Graceful degradation

If the Lean adapter subprocess fails (nonzero exit, timeout, `lake` not in PATH,
missing `.olean`, bad TSV output), `run_adapter()` returns `None`.

The comparator treats `None` as all fields absent:
- Fields where all adapters return `None` → `MISSING`
- Fields where other adapters have values but Lean returned `None` → `DIVERGE`

The harness never crashes on Lean failure.

---

## Smoke run output

```
python run.py --fixture complete_static_example --with-lean
```

```
FIELD                                       python    cpp-mosys   lean      VERDICT
protocol.name                               OpenTrackIO  OpenTrackIO  OpenTrackIO  PASS
protocol.version                            1.0.1     1.0.1       1.0.1     PASS
tracker.slate                               A101_A_4  A101_A_4    A101_A_4  PASS
tracker.serialNumber                        1234567890A  1234567890A  1234567890A  PASS
timing.timecode                             01:02:03:04  01:02:03:04  01:02:03:04  PASS
timing.sampleTimestamp.seconds              1718806554  1718806554  1718806554  PASS
timing.sampleTimestamp.nanoseconds          500000000  500000000   500000000  PASS
timing.sampleRate                           24        24          24        PASS
camera.activeSensorResolution.width         3840      3840        3840      PASS
camera.activeSensorResolution.height        2160      2160        2160      PASS
transforms.Camera.translation.x             1         1           1         PASS
transforms.Camera.translation.y             2         2           2         PASS
transforms.Camera.translation.z             3         3           3         PASS
transforms.Camera.rotation.pan              180       180         180       PASS
transforms.Camera.rotation.tilt             90        90          90        PASS
transforms.Camera.rotation.roll             45        45          45        PASS
lens.focusDistance                          10        10          10        PASS
lens.pinholeFocalLength                     null      24.305      24.305    DIVERGE

  pass=17  diverge=1  missing=0
```

17 PASS, 1 DIVERGE (`lens.pinholeFocalLength`). Lean agrees with C++ on the normative
value. Python diverges by reading the wrong key.

---

## Limitations and future work

- **Byte-level numeric spelling:** `json.load` normalizes numbers before the Lean
  literal is generated. The original JSON spelling is not preserved.
- **Float repr stability:** `repr(float)` is used for float→Lean conversion.
  This is deterministic and round-trip safe in Python 3.1+, but may differ from
  the fixture's original decimal rendering.
- **`transforms.Camera` lookup:** The Lean adapter finds the first transform whose
  `id = "Camera"`. If no such transform exists, all six transform fields are `null`.
- **Native `lake exe`:** Deferred (see Slice 17). The `lake env lean --run` path
  is sufficient for oracle comparison; native binary distribution is a separate concern.
- **Per-run latency:** Each fixture run invokes `lake env lean --run`, which loads
  the Lean runtime and imported `.olean` files. This takes 2–5 seconds per fixture.
  For large generated corpora, this adds up. A persistent runner process is future work.
