# battery-tester

Differential test harness for OpenTrackIO parser implementations.

Runs up to three adapters — Python, C++, and optionally a proof-backed Lean oracle — against the same canonical JSON fixtures and compares their output field-by-field. Divergences indicate real defects: implementations disagree on what the same input means.

## What it demonstrates

- Python and C++ agree on 17 of 18 comparison fields
- The Python parser (`opentrackio_lib.py`) reads `lens.focalLength` instead of `lens.pinholeFocalLength` — a real key-name bug exposed by the harness. This divergence is reproducible against the upstream SMPTE repo at [`5861818`](https://github.com/SMPTE/ris-osvp-metadata-camdkit/commit/5861818760d50b9ba984cef4e7b99c025396f874) (the last commit before the fix). Clone from upstream `main` before [PR#210](https://github.com/SMPTE/ris-osvp-metadata-camdkit/pull/210) merges and the `DIVERGE` will appear.
- The Lean adapter independently confirms the normative field name — its decoder is formally verified, so the key name is not a judgment call
- The harness degrades gracefully when the C++ binary or Lean toolchain is not available

## What it does not do

- CBOR or UDP input (JSON fixtures only)
- Full schema field coverage (18 comparison fields from the intersection)
- CI integration or machine-readable output
- Unit conversion (all values are raw from the JSON fixture)

## Setup

### Python dependencies

```sh
pip install cbor2 jsonschema hypothesis pytest
```

### Build — Mo-Sys C++ adapter (dump_sample)

Requires CMake ≥ 3.15 and nlohmann-json. On macOS:

```sh
brew install nlohmann-json
```

From `opentrackio-cpp/`:

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DOPENTRACKIO_BUILD_TOOLS=ON
cmake --build build --target dump_sample --config Release
```

Binary lands at: `build/tools/dump_sample/dump_sample`

## Run

From `battery-tester/`:

```sh
# Single canonical fixture — Python + C++
python run.py --fixture complete_static_example

# All four canonical fixtures — Python + C++
python run.py
```

Each run writes a dated sequential report file: `battery-tester-YYYY-MM-DD-N.txt`

### With the Lean oracle

Pass `--with-lean` to add the proof-backed Lean adapter as a third column:

```sh
# Single fixture — Python + C++ + Lean
python run.py --fixture complete_static_example --with-lean

# All four canonical fixtures — Python + C++ + Lean
python run.py --with-lean

# Generated corpus — Python + C++ + Lean
python run.py --generated --with-lean
```

Requires Lean 4 and Lake to be installed and `lake` in `PATH`. The Lean project must
be built at least once from `opentrackio-proof/`:

```sh
lake build
```

The Lean adapter runs `lake env lean --run` for each fixture. This takes 2–5 seconds
per fixture. If Lean is unavailable or fails, the harness continues and marks Lean
fields as diverging — no crash.

## Generated corpus

A parametric corpus of 76 fixtures can be generated to exercise the full value space of all 18 comparison fields — boundary values, mid-range values, and optional-field presence/absence combinations:

```sh
# Generate fixtures (writes to fixtures/generated/, not committed to git)
python generate_fixtures.py

# Run both adapters against the full corpus
python run.py --generated
```

The generated corpus covers: translation ±100 m, rotation ±179.999°, 5 sample rates, all timecode boundary values, epoch 0 through realistic timestamps, 4 sensor resolutions, 6 focal lengths, and one fixture each where `sampleTimestamp`, `activeSensorResolution`, `serialNumber`, and `pinholeFocalLength` are absent.

## Property tests

Hypothesis property tests verify the comparison logic invariants (PASS/DIVERGE/MISSING verdict rules, aggregate count correctness) without subprocesses:

```sh
python -m pytest tests/test_properties.py -v
```

## Demo walkthrough

**Flow 1 — single fixture table**
```
python run.py --fixture complete_static_example
```
Open the report file. See 18 fields compared across both adapters.

**Flow 2 — the divergence**
Find the `lens.pinholeFocalLength` row:
```
lens.pinholeFocalLength    null    24.305    DIVERGE
```
Python returns `null` because `opentrackio_lib.py:get_focal_length()` reads `lens.focalLength`,
which is not a key in the v1.0.1 schema. The C++ adapter correctly reads `lens.pinholeFocalLength`.

**Flow 3 — three-way with Lean**
```
python run.py --fixture complete_static_example --with-lean
```
The same divergence, now with a proof-backed third column:
```
lens.pinholeFocalLength    null    24.305    24.305    DIVERGE
```
Lean reads `24.305` for the same reason C++ does — the normative key `pinholeFocalLength`
is what the OpenTrackIO v1.0.1 schema specifies. The Lean decoder is formally verified:
if it reads a different key, the roundtrip theorem would not hold. Python's `null` is
not a verdict call by the harness; it is the measured output of an implementation
reading the wrong field name.

**Flow 4 — aggregate**
```
python run.py
```
Four fixture tables plus an aggregate. The divergence appears in every fixture that contains
`lens.pinholeFocalLength`. MISSING entries are expected for the "recommended" fixtures, which
intentionally omit many fields.

## Lean adapter

The Lean adapter is a proof-backed semantic oracle. It is not another parser implementation —
it is the formally verified OpenTrackIO data model from `opentrackio-proof/`, exercised
against the same 18 comparison fields.

**What it adds:**

- A third independent column in the comparison table, derived from the verified Lean decoder
- Confirmation that key names are normative: the Lean decoder was proved correct against the
  schema, so if it reads `lens.pinholeFocalLength` and Python reads `lens.focalLength`, the
  harness can attribute the divergence unambiguously
- Catches key-name bugs, missing-field bugs, and field-path bugs that are invisible to
  implementation-vs-implementation testing when both implementations share the same defect

**What it does not do:**

- It does not verify byte-level JSON parsing — Python's `json.load` converts the fixture
  before the Lean model sees it
- It does not replace the C++ or Python adapters
- It does not add new protocol semantics decisions; it reflects the verified model exactly

**Architecture:**

```
fixture.json
    └── json.load (Python)
            └── _py_to_lean(): Python JSON value → Lean JsonValue AST literal
                    └── lake env lean --run <generated runner>
                            └── decodeSample → Sample → 18 fields (TSV)
                                    └── parsed by Python → JSON dict
```

The Lean adapter is in `adapters/lean_adapter.py`. The Lean-side field extraction is
in `opentrackio_parser/HarnessAdapter.lean` (part of the `opentrackio-proof` project).

## Fixtures

Generated from camdkit at v1.0.1 and stored in `fixtures/`. They are not the "classic" examples
from the camdkit test resources (which are v0.9.3 and rejected by the Mo-Sys library).

## Comparison fields

| Field | Notes |
|---|---|
| `protocol.name` | String equality |
| `protocol.version` | String equality (`"1.0.1"`) |
| `tracker.slate` | String equality |
| `tracker.serialNumber` | Read from `static.tracker` by Python; from merged `sample.tracker` by C++ |
| `timing.timecode` | Zero-padded `HH:MM:SS:FF` |
| `timing.sampleTimestamp.seconds` | Epoch seconds (integer) |
| `timing.sampleTimestamp.nanoseconds` | Integer |
| `timing.sampleRate` | Float, tolerance 1e-9 |
| `camera.activeSensorResolution.width` | Integer pixels |
| `camera.activeSensorResolution.height` | Integer pixels |
| `transforms.Camera.translation.{x,y,z}` | Meters, float tolerance 1e-9 |
| `transforms.Camera.rotation.{pan,tilt,roll}` | Degrees, float tolerance 1e-9 |
| `lens.focusDistance` | Raw from JSON |
| `lens.pinholeFocalLength` | **Expected DIVERGE** — Python reads wrong key ([PR#210](https://github.com/SMPTE/ris-osvp-metadata-camdkit/pull/210)) |
