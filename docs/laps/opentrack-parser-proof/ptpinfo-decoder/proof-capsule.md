# Proof Capsule — ptpinfo-decoder (Slice 14.4)

## Intent

Define `decodePtpInfo : JsonValue → Except DecodeError PtpInfo`.
Six required fields, two optional. Uses `decodeLeaderPriorities` (Slice 14.1)
and the enum decoders `decodePtpProfile` / `decodePtpLeaderSource` (Slice 7).
`leaderIdentity` requires a nonempty string, enforced at construction.
No theorems — the only invariant (`leaderIdentity.val ≠ ""`) is carried by
`NonemptyString` and proved at construction.

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/PtpInfoDecoder.lean` | `PtpInfoDecoder` |

One new `[[lean_lib]]` entry appended after `TrackerDecoder` in `lakefile.toml`.

## Imports

```lean
import DecodeError
import JsonRawModel
import TransformModel
import TimingEnumDecoders
import LeafDecoders
import SampleModel
```

## Frozen formal statement

```lean
def decodePtpInfo (j : JsonValue) : Except DecodeError PtpInfo
```

Accepts a `JsonValue.object`. The six required fields produce `.error` when
absent. The two optional fields produce `none` when absent.

## Field specification

| Field | JSON type | Required | Lean type | Decoder |
|---|---|---|---|---|
| `profile` | string (enum) | ✅ | `PtpProfile` | `decodePtpProfile` |
| `domain` | number (integer) | ✅ | `String` | raw number string |
| `leaderIdentity` | string (nonempty) | ✅ | `NonemptyString` | `if h : s ≠ ""` |
| `leaderPriorities` | object | ✅ | `LeaderPriorities` | `decodeLeaderPriorities` |
| `leaderAccuracy` | number | ✅ | `String` | raw number string |
| `meanPathDelay` | number | ✅ | `String` | raw number string |
| `leaderTimeSource` | string (enum) | optional | `Option PtpLeaderSource` | `decodePtpLeaderSource` |
| `vlan` | number (integer) | optional | `Option String` | raw number string |

## No theorems

`NonemptyString` is constructed with `⟨s, h⟩` where `h : s ≠ ""`.
No additional soundness theorem needed for an all-`Option`-or-`String` result.

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No new struct definitions.
- No changes to Slices 1–14.3.

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/PtpInfoDecoder.lean` — exit 0, no warnings.
2. `lake build PtpInfoDecoder` — exit 0.
3. No `sorry` or forbidden constructs.
