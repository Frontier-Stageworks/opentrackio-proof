# Proof Review — integration-smoke (Slice 12-pre)

## Kernel status

`lake env lean opentrackio_parser/IntegrationSmoke.lean` — exit 0, no warnings.
All five `#eval` lines printed `true`.
`lake build IntegrationSmoke` — exit 0 (7.3s, 3302 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No `open Classical`.
- No new theorems.
- No changes to Slices 1–11.

## Import audit

All 16 parser modules imported in dependency order:

| # | Module | Slice |
|---|---|---|
| 1 | `RationalValueWrappers` | 1 |
| 2 | `JsonRawModel` | 2 |
| 3 | `DecodeError` | 3 |
| 4 | `ProtocolVersion` | 4A |
| 5 | `VersionDecoder` | 4B |
| 6 | `ProtocolDecoder` | 4C |
| 7 | `RationalDecoder` | 5 |
| 8 | `NonemptyArrayDecoder` | 6 |
| 9 | `TimingEnumDecoders` | 7 |
| 10 | `TransformModel` | 8A |
| 11 | `TransformDecoder` | 8B |
| 12 | `CameraModel` | 9A |
| 13 | `CameraDecoder` | 9B |
| 14 | `LensModel` | 10A |
| 15 | `LensDecoder` | 10B |
| 16 | `SampleModel` | 11 |

No import cycle errors. Elaboration of all 16 transitively succeeds.

## Component audit

| # | Decoder | Input shape | Output |
|---|---|---|---|
| 1 | `decodeProtocol` | `{name: "OpenTrackIO", version: [1,0,1]}` | `true` |
| 2 | `decodePositiveRational` | `{num: 24000, denom: 1001}` | `true` |
| 3 | `decodeTransform` | `{translation, rotation, id: "cam1"}` | `true` |
| 4 | `decodeCamera` | `{captureFrameRate: {24/1}, make: "ARRI"}` | `true` |
| 5 | `decodeLens` | `{encoders: {focus: 0.5, iris: 0.3, zoom: 0.1}}` | `true` |

Invariant-carrying types verified through decoders:
- `PositiveRational` in `captureFrameRate` (Component 4)
- `NonemptyString` in `make` (Component 4)
- `FizOptions.anyPresent` in `encoders` (Component 5)
- `NonemptyString` in `id` (Component 3)

## Shell construction audit

`smokeSample : Sample` elaborates without error. `Except.toOption` correctly
extracts `Option α` from both decoder results. `Option.map` threads the camera
value into `StaticInfo` without a proof obligation. `«static»` guillemet
syntax accepted in record literal position (consistent with Slice 11).

## Capsule deviations (recorded)

| Capsule statement | Actual plan/code |
|---|---|
| `decodeProtocol (.object [("protocol", ...)])` | Corrected to `decodeProtocol (.object [("name", ...), ("version", ...)])` — capsule omitted required `"name"` field |
| `#eval native_decide (... \|>.isOk = true)` | Changed to `#eval ... \|>.isOk` — `native_decide` is tactic-only; plain `#eval` on `Bool` is correct |

Both deviations are refinements that bring the code into conformance with the
actual decoder signatures. No behavioral change.

## Contract compliance

1. ✅ All 16 modules imported; no elaboration failures.
2. ✅ No `sorry` or forbidden constructs.
3. ✅ `lake env lean` exit 0, no warnings.
4. ✅ `lake build IntegrationSmoke` exit 0.
5. ✅ All five `#eval` lines print `true`.
6. ✅ `smokeSample` elaborates without `sorry`.
7. ✅ No changes to Slices 1–11.
