# opentrackio_parser — Parser Verification

Lean 4 formal model of the [OpenTrackIO](https://github.com/SMPTE/ris-osvp-metadata-camdkit)
v1.0.1 JSON sample data model over the project's `JsonValue` AST model: decoders,
encoders, roundtrip theorems, a `WellFormedSampleJson` predicate,
normalization/idempotence theorems, and an executable harness.

This is not a verified byte-level JSON parser. The model operates on an already-parsed
`JsonValue` AST. Byte-level JSON parsing, numeric upper bounds, regex constraints, and
full schema conformance checking are explicitly outside the proved core.

---

## What is proved

### Encode/decode roundtrip

```lean
theorem encodeSample_roundtrip (s : Sample) :
    decodeSample (encodeSample s) = .ok s
```

The strongest single artifact. For any `Sample` value constructible in the model,
encoding it and decoding the result returns the original value. Rules out encoder
field-name bugs, missing-field bugs, and key-spelling bugs end-to-end. This is hard
to fake: a constant encoder or constant decoder would fail for populated `Sample` values.

Depends on `nat_repr_toNat?_some` — a nontrivial standalone lemma proving that Lean's
decimal renderer and `String.toNat?` are inverses for all natural numbers.

### Decoder soundness — type-carried structural invariants

Five theorems lift component invariants to the full-sample level:

```lean
theorem decodeSample_transforms_sound    ... : ts.values ≠ []
theorem decodeSample_protocol_sound      ... : ValidVersion p.version
theorem decodeSample_lens_encoders_sound ... : fiz.focus ≠ none ∨ fiz.iris ≠ none ∨ fiz.zoom ≠ none
theorem decodeSample_static_duration_sound : 0 < r.toReal
theorem decodeSample_static_camera_sound   : 0 < r.toReal
```

These theorems are short because the invariants are type-carried: `PositiveRational`
carries `num_pos` and `den_pos`, `NonemptyArray` carries `nonempty`, `Fin 10` bounds
version digits, `NonemptyString` carries `nonempty`, and `FizOptions.anyPresent` is a
real disjunctive constraint. The decoder is the enforcement point; invalid states
cannot be constructed.

### Error correctness — required-field rejection

Five theorems prove that specific missing-field inputs produce specific error tags:

```lean
theorem decodeProtocol_missing_name        : ... = .error (.missingField "name")
theorem decodeProtocol_missing_version     : ... = .error (.missingField "version")
theorem decodeTransform_missing_translation: ... = .error (.missingField "translation")
theorem decodeTransform_missing_rotation   : ... = .error (.missingField "rotation")
theorem decodePositiveRational_missing_num : ... = .error (.missingField "num")
```

The listed required-field cases are proved to reject with the expected error tags.

### Closed-world enum decoding

`TimingMode`, `SyncSource`, `PtpProfile`, and `PtpLeaderSource` are decoded from
exact string literals. Unknown strings cause decode failure. Each decoder is paired
with a `toStr` roundtrip theorem proving the decoder and renderer are inverses.

### Normalization

```lean
theorem sampleNormalize_idempotent (j : JsonValue) :
    sampleNormalize (sampleNormalize j) = sampleNormalize j

theorem normalization_under_wellFormed (j : JsonValue) (s : Sample)
    (_ : WellFormedSampleJson j) (hd : decodeSample j = .ok s) :
    decodeSample (sampleNormalize j) = .ok s
```

`sampleNormalize_idempotent` derives nontrivially from `encodeSample_roundtrip`.
`normalization_under_wellFormed` preserves decoded semantics for well-formed inputs;
the `WellFormedSampleJson` hypothesis is a domain label — it marks intended application
rather than doing load-bearing proof work.

---

## What is not proved

| Limitation | Notes |
|---|---|
| Byte-level JSON parsing | `json.load` or equivalent is outside scope; model operates on an already-parsed AST |
| `WellFormedSampleJson (encodeSample s)` | Not proved — private-predicate access boundary between `WellFormedSampleJson.lean` and `NormalizationTheorems.lean` |
| Numeric upper bounds | `PositiveRational` enforces positivity; frame rate ≤ 240, angle ranges, pixel count limits are not proved |
| Regex / pattern constraints | UUID URNs, PTP leader identities, firmware strings stored as raw `String` |
| Duplicate-key enforcement in `decodeSample` | Modeled by `NoDupKeys` in `WellFormedSampleJson`; `decodeSample` itself does not reject duplicates — `lookup?` takes the first match |
| Decode → re-encode normalization | `encodeSample_roundtrip` proves encode → decode; the inverse direction is covered by `sampleNormalize_idempotent` only after one normalize pass |

---

## Module structure

| File | Layer | Role |
|---|---|---|
| `RationalValueWrappers.lean` | 0 | `PositiveRational`, `NonnegativeRational`, `RationalWithPositiveDenominator` — invariant-carrying types |
| `JsonRawModel.lean` | 0 | `JsonValue` AST; `lookup?` utility |
| `DecodeError.lean` | 0 | `DecodeError` inductive — error vocabulary |
| `ProtocolVersion.lean` / `VersionDecoder.lean` / `ProtocolDecoder.lean` / `VersionEncoder.lean` | 1 | `VersionDigit := Fin 10`; `decodeVersionDigit`, `decodeVersionValue`, `decodeProtocol` |
| `RationalDecoder.lean` | 1 | `decodePositiveRational`; soundness via `if hn :` / `if hd :` decision proofs |
| `NonemptyArrayDecoder.lean` | 1 | `NonemptyArray`; `decodeNonemptyArray` |
| `TimingEnumDecoders.lean` | 1 | Closed-world decoders for `TimingMode`, `SyncSource`, `PtpProfile`, `PtpLeaderSource` |
| `TransformModel.lean` / `TransformDecoder.lean` / `TransformEncoder.lean` | 2 | `NonemptyString`; `Transform`; `decodeTransform` |
| `CameraModel.lean` / `CameraDecoder.lean` / `CameraEncoder.lean` | 2 | `SensorResolution`; `Camera`; `decodeCamera` |
| `LensModel.lean` / `LensDecoder.lean` / `LensEncoder.lean` / `LensSubEncoders.lean` | 2 | `FizOptions.anyPresent`; `Lens`; `decodeLens` — reads `pinholeFocalLength`, not `focalLength` |
| `SampleModel.lean` | 2 | Full `Sample` struct; all field names and types |
| `IntegrationSmoke.lean` | 2 | Five `#eval` executable witnesses; `smokeSample` construction |
| `SampleDecoder.lean` | 3 | `decodeSample`; five composed soundness theorems |
| `ErrorCorrectness.lean` | 4 | Five required-field rejection theorems |
| `*Encoder.lean` (multiple) | 5 | Encoders for all sub-models; `encodeSample` |
| `NumericLiteralRoundtrip.lean` | 5 | `nat_repr_toNat?_some` — decimal renderer / `toNat?` inverse |
| `WellFormedSampleJson.lean` | 6 | `WellFormedSampleJson` predicate; `NoDupKeys` |
| `NormalizationTheorems.lean` | 6 | `sampleNormalize`; idempotence and decode-preservation theorems |
| `HarnessMain.lean` | 6 | Executable harness — 10 checks, all PASS |
| `HarnessAdapter.lean` | 6 | Battery-tester oracle — extracts 18 comparison fields via `decodeSample` |

---

## Running the harness

```sh
lake env lean --run opentrackio_parser/HarnessMain.lean
```

or the convenience wrapper from the repo root:

```sh
scripts/opentrackio-harness.sh
```

Expected output: 10 checks, all `PASS`.

Native `lake exe` is deferred due to a Lean 4.29.0 / Darwin 25.3.0 toolchain linker
incompatibility. All stated Lean proof obligations in this parser project are fully discharged; this is
a packaging limitation only.

---

## Further reading

- [Anti-vacuity audit](../docs/opentrack-parser-proof/anti-vacuity-audit.md) — theorem-level analysis of proof strength, known weak spots, and deferred limitations
- [Work queue](../docs/opentrack-parser-proof/opentrack-parser-verification/work-queue.md) — full 18-slice development history
