# Proof Capsule — timecode-decoder (Slice 14.5)

## Intent

Define `decodeTimecode : JsonValue → Except DecodeError Timecode`.
Five required fields (`hours`, `minutes`, `seconds`, `frames` as raw number strings;
`frameRate` via `decodePositiveRational`), two optional fields (`subFrame` as raw number
string, `dropFrame` as `Option Bool`). No theorems.

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/TimecodeDecoder.lean` | `TimecodeDecoder` |

One new `[[lean_lib]]` entry appended after `PtpInfoDecoder` in `lakefile.toml`.

## Imports

```lean
import DecodeError
import JsonRawModel
import SampleModel
import RationalDecoder
```

## Frozen formal statement

```lean
def decodeTimecode (j : JsonValue) : Except DecodeError Timecode
```

Accepts a `JsonValue.object`. The five required fields produce `.error` when absent.
The two optional fields produce `none` when absent.

## Field specification

| Field | JSON type | Required | Lean type | Decoder |
|---|---|---|---|---|
| `hours` | number | ✅ | `String` | raw number string |
| `minutes` | number | ✅ | `String` | raw number string |
| `seconds` | number | ✅ | `String` | raw number string |
| `frames` | number | ✅ | `String` | raw number string |
| `frameRate` | object | ✅ | `PositiveRational` | `decodePositiveRational` |
| `subFrame` | number | optional | `Option String` | raw number string, pure `let` |
| `dropFrame` | bool | optional | `Option Bool` | `.bool b`, pure `let` |

## No theorems

All invariants (`frameRate` positivity) are in `PositiveRational`'s type.
No additional soundness proof needed.

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No new struct definitions.
- No changes to Slices 1–14.4.

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/TimecodeDecoder.lean` — exit 0, no warnings.
2. `lake build TimecodeDecoder` — exit 0.
3. No `sorry` or forbidden constructs.
