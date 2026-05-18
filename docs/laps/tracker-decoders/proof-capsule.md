# Proof Capsule — tracker-decoders (Slice 14.3)

## Intent

Define `decodeStaticTracker` and `decodeTracker`. Both structs have only
optional fields: `NonemptyString` fields use the established
`decodeOptionalString` pattern; `recording : Option Bool` uses `JsonValue.bool`.
No invariant-carrying types beyond `NonemptyString`. No theorems — the only
invariant (`val ≠ ""`) is already carried by the type and proved by construction.

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/TrackerDecoder.lean` | `TrackerDecoder` |

One new `[[lean_lib]]` entry appended after `GlobalStageDecoder` in `lakefile.toml`.

## Imports

```lean
import DecodeError
import JsonRawModel
import TransformModel
import SampleModel
```

`TransformModel` provides `NonemptyString`.

## Frozen formal statements

### D1 — StaticTracker decoder

```lean
def decodeStaticTracker (j : JsonValue) : Except DecodeError StaticTracker
```

Four optional `NonemptyString` fields: `make`, `model`, `serialNumber`,
`firmwareVersion`. All decode via the `decodeOptionalString` pattern.

### D2 — Tracker decoder

```lean
def decodeTracker (j : JsonValue) : Except DecodeError Tracker
```

Three optional `NonemptyString` fields (`notes`, `slate`, `status`) plus one
optional `Bool` field (`recording`). The `Bool` field uses `JsonValue.bool`
and is a pure `let` (absent or wrong-type → `none`, no error).

## Helper

`decodeOptionalString` is `private` in `CameraDecoder` and `LensDecoder`.
Re-defined as a `private` helper in this file — same logic, same contract.

## No theorems

`NonemptyString` nonemptiness is enforced at construction; no additional
soundness theorem is needed for all-optional decoders.

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No new struct definitions.
- No changes to Slices 1–14.2.

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/TrackerDecoder.lean` — exit 0, no warnings.
2. `lake build TrackerDecoder` — exit 0.
3. No `sorry` or forbidden constructs.
