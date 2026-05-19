# Proof Capsule — globalstage-encoder (Slice 15.3)

## Intent

Define `encodeGlobalStage : GlobalStage → JsonValue` and prove
`decodeGlobalStage (encodeGlobalStage g) = .ok g`.

`GlobalStage` has six required number fields and no optional fields or
invariant-carrying types. This is the simplest encoder slice.

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/GlobalStageEncoder.lean` | `GlobalStageEncoder` |

One new `[[lean_lib]]` entry appended after `TransformEncoder` in `lakefile.toml`.

## Imports

```lean
import DecodeError
import JsonRawModel
import SampleModel
import GlobalStageDecoder
```

## Frozen formal statements

```lean
def encodeGlobalStage (g : GlobalStage) : JsonValue

theorem encodeGlobalStage_roundtrip (g : GlobalStage) :
    decodeGlobalStage (encodeGlobalStage g) = .ok g
```

## Encoder specification

```
encodeGlobalStage g = .object [
  ("E",    .number g.E),
  ("N",    .number g.N),
  ("U",    .number g.U),
  ("lat0", .number g.lat0),
  ("lon0", .number g.lon0),
  ("h0",   .number g.h0)
]
```

## Proof strategy

`simp [encodeGlobalStage, decodeGlobalStage, JsonValue.lookup?]; rfl`

Fixed-shape object; `simp` reduces all `lookup?` matches; `rfl` closes the
residual `Except.bind` chain (established pattern from Slice 15.2).

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No new struct definitions.
- No changes to Slices 1–14.8.

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/GlobalStageEncoder.lean` — exit 0, no warnings.
2. `lake build GlobalStageEncoder` — exit 0.
3. No `sorry` or forbidden constructs.
4. Roundtrip theorem green.
