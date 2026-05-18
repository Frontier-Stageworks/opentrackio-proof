# Proof Review — compose-decoder-soundness / 12A: decodeSampleShell

## Kernel status

`lake env lean opentrackio_parser/SampleDecoder.lean` — exit 0, no warnings.
`lake build SampleDecoder` — exit 0 (2.7s, 3302 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No theorems (deferred to 12B).
- No new struct definitions.
- No changes to Slices 1–11.5.

## Plan deviations (recorded)

| Plan | Actual | Reason |
|---|---|---|
| Nested `do` block for `staticInfo` | Extracted to `private def decodeStaticInfo` | Lean 4 elaborator could not resolve return type of `return some { ... }` inside nested `do` |
| Lambda `fun (ej : JsonValue) : Except DecodeError String =>` | Extracted to `private def decodeRelatedId` | Return type ascription on `fun` with `match` body rejected by parser |

Both deviations are minimal structural refactors. The logic is identical to the plan.

## Field coverage audit

| Sample field | Handling | Status |
|---|---|---|
| `protocol` | `decodeProtocol vj` | ✅ wired |
| `lens` | `decodeLens vj` | ✅ wired |
| `transforms` | `decodeNonemptyArray decodeTransform "transforms" vj` | ✅ wired |
| `sampleId` | `.string s → some s` | ✅ raw string |
| `sourceId` | `.string s → some s` | ✅ raw string |
| `sourceNumber` | `.number s → some s` | ✅ raw number string |
| `relatedSampleIds` | `mapM decodeRelatedId` | ✅ array of strings |
| `«static».duration` | `decodePositiveRational vj` | ✅ wired |
| `«static».camera` | `decodeCamera vj` | ✅ wired |
| `«static».lens` | `decodeStaticLens vj` | ✅ wired |
| `«static».tracker` | `none` | ⏸ deferred |
| `timing` | `none` | ⏸ deferred |
| `tracker` | `none` | ⏸ deferred |
| `globalStage` | `none` | ⏸ deferred |

## Private helper audit

| Name | Role |
|---|---|
| `decodeRelatedId` | Single `JsonValue → Except DecodeError String` for `mapM` on `relatedSampleIds` array |
| `decodeStaticInfo` | Decodes the `static` sub-object; wires `duration`, `camera`, `lens`; `tracker := none` |

## Contract compliance

1. ✅ `lake env lean` exit 0, no warnings.
2. ✅ `lake build SampleDecoder` exit 0.
3. ✅ No `sorry` or forbidden constructs.
4. ✅ No theorems.
5. ✅ No new struct definitions.
6. ✅ No changes to Slices 1–11.5.
7. ✅ All fields from capsule covered; deferred fields produce `none`.
