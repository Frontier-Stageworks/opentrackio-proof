# Proof Capsule — globalstage-decoder (Slice 14.2)

## Intent

Define `decodeGlobalStage : JsonValue → Except DecodeError GlobalStage`.
All six fields are required JSON numbers stored as raw strings. No
invariant-carrying types; no theorems.

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/GlobalStageDecoder.lean` | `GlobalStageDecoder` |

One new `[[lean_lib]]` entry appended after `LeafDecoders` in `lakefile.toml`.

## Frozen formal statement

```lean
def decodeGlobalStage (j : JsonValue) : Except DecodeError GlobalStage
```

Accepts a `JsonValue.object`. All six fields (`E`, `N`, `U`, `lat0`, `lon0`,
`h0`) are required JSON numbers. Absent or wrong-type fields produce `.error`.

## Field types (per A4/A8 sample resolution)

| Field | JSON type | Lean type |
|---|---|---|
| `E` | number (required) | `String` |
| `N` | number (required) | `String` |
| `U` | number (required) | `String` |
| `lat0` | number (required) | `String` |
| `lon0` | number (required) | `String` |
| `h0` | number (required) | `String` |

## No theorems

All fields are raw `String`. No invariant-carrying types; nothing non-trivial
to prove.

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No new struct definitions.
- No changes to Slices 1–14.1.

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/GlobalStageDecoder.lean` — exit 0, no warnings.
2. `lake build GlobalStageDecoder` — exit 0.
3. No `sorry` or forbidden constructs.
