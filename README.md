# opentrackio-proof

Lean 4 formal verification of the OpenTrackIO protocol and the OpenCV ↔ OpenTrackIO
camera parameter conversion theorems.

The repo contains four projects. They share a single Lean toolchain and Lake build.

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

Lean 4 formal model of the [OpenTrackIO](https://github.com/SMPTE/ris-osvp-metadata-camdkit)
v1.0.1 JSON sample data model over a verified `JsonValue` AST: decoders, encoders,
roundtrip theorems, a `WellFormedSampleJson` predicate, normalization/idempotence theorems,
and an executable harness.

Key properties proved:

- `encodeSample_roundtrip` — encoding a `Sample` and then decoding it returns
  the original `Sample`
- `decodeSample` soundness theorems — decoded samples preserve the model's
  type-carried structural invariants, including positive rationals, nonempty
  arrays, valid protocol-version digits, nonempty strings, and lens encoder
  presence constraints
- `sampleNormalize_idempotent` — normalization is stable after one pass
- `normalization_under_wellFormed` — normalization preserves decoded semantics
  for well-formed inputs
- Lean harness / battery-tester adapter support extraction of the 18 comparison
  fields used by the differential harness

The harness runs via:

```sh
lake env lean --run opentrackio_parser/HarnessMain.lean
```

or the convenience wrapper:

```sh
scripts/opentrackio-harness.sh
```

Native `lake exe` is deferred due to a Lean 4.29.0 / Darwin 25.3.0 toolchain
linker incompatibility. All Lean proof obligations in the repository are fully
discharged.

This is not a verified byte-level JSON parser. Byte-level JSON parsing, some
numeric upper bounds, regex constraints, and full schema conformance checking are
explicitly outside the proved parser core.

[Full details](opentrackio_parser/README.md)

---

## openlensio_semantics — Lens model semantics

Lean 4 formal verification of the [OpenLensIO](https://openlensio.org) v1.0.1
Brown-Conrady distortion pipeline (D→U direction). 14 public theorems across
11 source files, all proved over exact reals (ℝ) using Mathlib's noncomputable
infrastructure.

Key definitions:

- `RadialCoefficients` — k1–k6 coefficients in alternating numerator/denominator
  form matching the OpenLensIO rational polynomial layout
- `TangentialCoefficients` — p1, p2 tangential distortion coefficients
- `LensSemantics` / `ValidLensSemantics` — lens parameter record with
  `0 < focalLength` validity predicate
- `undistortPoint` — full Brown-Conrady undistortion with `denominatorNonzero`
  domain predicate
- `undistortFromDistorted` / `fovUndistortFromDistorted` — projection-matrix form
  (Eq 4) and FOV form (Eq 10) undistortion

Key theorems:

- `brown_conrady_zero_identity` — all-zero coefficients reduce undistortion to identity
- `distortion_center_translation_commutes` — the ΔP principal-point offset cancels
  in the undistortion argument (load-bearing lemma for FOV ↔ projection consistency)
- `fov_undistort_eq` — Eq (10) is structurally consistent with Eq (4) under the
  ΔP coordinate translation (Eq 13)
- `pixel_metric_roundtrip` / `image_texture_coordinate_roundtrip` — sensor
  coordinate space conversions are exact inverses
- `semanticExtraction_sound` — lens parameter extraction from raw data satisfies
  `ValidLensSemantics`

Central finding: OpenLensIO and OpenCV tangential distortion operate in different
coordinate frames. Coefficient equality does not imply semantic equivalence; the
formal model makes this distinction explicit.

An executable float-layer oracle (`ExecutableSemanticOracle.lean`) and a Python
reference implementation (`battery-tester/semantic_oracle/reference_oracle.py`)
are provided for differential validation. The oracle layer is not formally proved
— it bridges to the exact-real layer for verification.

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
