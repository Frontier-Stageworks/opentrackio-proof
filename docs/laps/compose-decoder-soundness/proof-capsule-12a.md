# Proof Capsule — compose-decoder-soundness / 12A: decodeSampleShell

## Intent

Define `decodeSample : JsonValue → Except DecodeError Sample` that wires
existing component decoders to the fields of `Sample`. Fields with existing
decoders are decoded; fields with no decoder yet produce `none`. No new
sub-object decoders are introduced in this slice. No theorems.

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/SampleDecoder.lean` | `SampleDecoder` |

One new `[[lean_lib]]` entry appended after `SampleModel` (and before
`IntegrationSmoke`) in `lakefile.toml`.

## What is decoded in 12A

Fields with existing decoders that 12A will wire:

| Sample field | Decoder used |
|---|---|
| `protocol` | `decodeProtocol` (ProtocolDecoder) |
| `lens` | `decodeLens` (LensDecoder) |
| `transforms` | `decodeNonemptyArray decodeTransform` (NonemptyArrayDecoder + TransformDecoder) |
| `«static».duration` | `decodePositiveRational` (RationalDecoder) |
| `«static».camera` | `decodeCamera` (CameraDecoder) |
| `«static».lens` | `decodeStaticLens` (LensDecoder) |

Fields handled as raw optional strings / lists (no sub-decoder needed):

| Sample field | Handling |
|---|---|
| `sampleId` | `lookup?` → `.string s → some s` |
| `sourceId` | same |
| `sourceNumber` | same |
| `relatedSampleIds` | `lookup?` → `.array` → `List.mapM` extract strings |

Fields deferred (no decoder yet — always produce `none` in 12A):

| Sample field | Reason |
|---|---|
| `timing` | No timing sub-decoder exists |
| `tracker` | No tracker sub-decoder exists |
| `globalStage` | No globalStage sub-decoder exists |
| `«static».tracker` | No staticTracker sub-decoder exists |

## Frozen formal statement

```lean
def decodeSample (j : JsonValue) : Except DecodeError Sample
```

Accepted input: `JsonValue.object`. All top-level fields are optional; a
missing key produces `none`. A present key that fails its sub-decoder
produces `.error`. An absent top-level `static` key produces `none` for
the whole `StaticInfo`.

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No theorems (deferred to 12B).
- No new struct definitions (all types already exist in Slices 1–11).
- No changes to Slices 1–11.5.

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.
Do not introduce new sub-object decoders mid-slice — add a sub-queue entry
instead.

## Acceptance criteria

1. `lake env lean opentrackio_parser/SampleDecoder.lean` — exit 0, no warnings.
2. `lake build SampleDecoder` — exit 0.
3. No `sorry` or forbidden constructs.
4. No theorems in this file.
