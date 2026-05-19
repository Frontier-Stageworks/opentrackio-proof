# opentrackio-proof

Lean 4 formal verification of the OpenTrackIO protocol and the OpenCV ↔ OpenTrackIO
camera parameter conversion theorems.

The repo contains three projects. They share a single Lean toolchain and Lake build.

---

## opencv_opentrackio_proofs — Conversion theorem proofs

15 theorems proving that the OpenCV ↔ OpenTrackIO lens calibration parameter
conversions from the SMPTE RIS paper are mathematically correct and unique
(necessary, not merely sufficient).

Covers the principal-point conversion, all radial and tangential distortion
parameter conversions, and end-to-end pixel coordinate preservation.

[Full details](opencv_opentrackio_proofs/README.md)

---

## opentrackio_parser — Parser verification

Lean 4 formal model of the full OpenTrackIO v1.0.1 JSON sample schema:
decoders, encoders, roundtrip theorems, a `WellFormedSampleJson` predicate,
normalization theorems, and an executable harness.

Key properties proved:

- `encodeSample_roundtrip` — encode then decode returns the original `Sample`
- `decodeSample_sound` — decode succeeds only when the input is well-formed
- `normalization_under_wellFormed` — normalization is a no-op on already-well-formed samples
- All 18 comparison fields extracted by the executable harness

The harness runs via:

```sh
lake env lean --run opentrackio_parser/HarnessMain.lean
```

or the convenience wrapper:

```sh
scripts/opentrackio-harness.sh
```

Native `lake exe` is deferred due to a Lean 4.29.0 / Darwin 25.3.0 toolchain
linker incompatibility. All proof obligations are fully discharged.

---

## battery-tester — Differential test harness

Runs the Python camdkit adapter, the Mo-Sys C++ adapter, and optionally the
proof-backed Lean oracle against the same canonical JSON fixtures, then compares
their output field-by-field across 18 comparison fields.

```sh
# Python + C++
python run.py

# Python + C++ + Lean (proof-backed oracle)
python run.py --with-lean

# Single fixture, three-way
python run.py --fixture complete_static_example --with-lean
```

Exposes real implementation bugs — the harness currently finds a key-name defect
in the Python camdkit adapter (`lens.focalLength` vs `lens.pinholeFocalLength`),
independently confirmed by the Lean oracle.

[Full details](battery-tester/README.md)

---

## Building

Requires [elan](https://github.com/leanprover/elan).

```sh
lake update   # downloads Mathlib (~1 GB cache, one-time)
lake build
```

Expected: `Build completed successfully (3310 jobs).`
