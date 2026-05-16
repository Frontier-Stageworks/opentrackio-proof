# battery-tester

Differential test harness for OpenTrackIO parser implementations.

Runs three parser adapters against the same canonical JSON fixtures and compares their output field-by-field. Divergences indicate real defects — the parser implementations disagree on what the same input means.

## What it demonstrates

- All three parser surfaces agree on transform, timing, tracker, protocol, and lens fields
- The Python parser (`opentrackio_lib.py`) reads `lens.focalLength` instead of `lens.pinholeFocalLength` — a real key-name bug exposed by the harness
- The harness degrades gracefully when a C++ adapter binary is not yet built

## What it does not do

- CBOR or UDP input (JSON fixtures only)
- Full schema field coverage (18 comparison fields)
- CI integration or machine-readable output
- Unit conversion (all values are raw from the JSON fixture)

## Architecture note

The CamDKit C++ adapter (`cpp-camdkit`) wraps the Mo-Sys opentrackio-cpp library — it is not an independent parse path. Both C++ adapters use `OpenTrackIOSample` under the hood. The Python adapter is the only truly independent implementation.

## Setup

### Python dependencies

```sh
pip install cbor2 jsonschema
```

### Build — Mo-Sys C++ adapter (dump_sample)

Requires Conan 2 and CMake ≥ 3.15. From `opentrackio-cpp/`:

```sh
pip install conan
conan profile detect          # first time only
conan install . --build=missing -s compiler.cppstd=20 -s build_type=Release
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DOPENTRACKIO_BUILD_TOOLS=ON
cmake --build build --target dump_sample --config Release
```

Binary lands at: `build/tools/dump_sample/dump_sample`

### Build — CamDKit C++ adapter

Requires Conan 2 and CMake ≥ 3.30. From `ris-osvp-metadata-camdkit/src/test/cpp/opentrackio-parser/`:

```sh
conan install . --build=missing -s compiler.cppstd=20 -s build_type=Release
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build --target opentrackio-parser --config Release
```

Binary lands at: `build/opentrackio-parser`

## Run

From `battery-tester/`:

```sh
# Single fixture
python run.py --fixture complete_static_example

# All four fixtures
python run.py
```

Each run writes a dated sequential report file: `battery-tester-YYYY-MM-DD-N.txt`

## Demo walkthrough

**Flow 1 — single fixture table**
```
python run.py --fixture complete_static_example
```
Open `battery-tester-YYYY-MM-DD-1.txt`. See 18 fields compared across three adapters.

**Flow 2 — the divergence**
Find the `lens.pinholeFocalLength` row:
```
lens.pinholeFocalLength        null               24.305             24.305             DIVERGE
```
Python returns `null` because `opentrackio_lib.py:get_focal_length()` reads `lens.focalLength`,
which is not a key in the current schema. Both C++ adapters correctly read `lens.pinholeFocalLength`.

**Flow 3 — aggregate**
```
python run.py
```
Open `battery-tester-YYYY-MM-DD-2.txt`. Four fixture tables plus an aggregate showing cumulative
pass/diverge/missing counts.

## Comparison fields

| Field | Notes |
|---|---|
| `protocol.name` | String equality |
| `protocol.version` | String equality (e.g. `"0.9.3"`) |
| `tracker.slate` | String equality |
| `tracker.serialNumber` | Read from `static.tracker` by Python; from `sample.tracker` by C++ |
| `timing.timecode` | Zero-padded `HH:MM:SS:FF` |
| `timing.sampleTimestamp.seconds` | Epoch seconds (integer) |
| `timing.sampleTimestamp.nanoseconds` | Integer |
| `timing.sampleRate` | Float, tolerance 1e-9 |
| `camera.activeSensorResolution.width` | Integer pixels |
| `camera.activeSensorResolution.height` | Integer pixels |
| `transforms.Camera.translation.{x,y,z}` | Meters, float tolerance 1e-9 |
| `transforms.Camera.rotation.{pan,tilt,roll}` | Degrees, float tolerance 1e-9 |
| `lens.focusDistance` | Raw from JSON |
| `lens.pinholeFocalLength` | **Expected DIVERGE** — Python reads wrong key |
