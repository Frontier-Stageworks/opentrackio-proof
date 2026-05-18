# Proof Capsule — leaf-encoders (Slice 15.1)

## Intent

Define encoders for `Timestamp`, `LeaderPriorities`, and `SyncOffsets` and prove
`decode (encode x) = .ok x` for each. These are the three leaf object types decoded
in `LeafDecoders.lean` (Slice 14.1). No invariant-carrying types involved.

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/LeafEncoders.lean` | `LeafEncoders` |

One new `[[lean_lib]]` entry appended after `VersionEncoder` in `lakefile.toml`.

## Imports

```lean
import DecodeError
import JsonRawModel
import SampleModel
import LeafDecoders
```

## Frozen formal statements

```lean
def encodeTimestamp       (t  : Timestamp)        : JsonValue
def encodeLeaderPriorities (lp : LeaderPriorities) : JsonValue
def encodeSyncOffsets      (so : SyncOffsets)      : JsonValue

theorem encodeTimestamp_roundtrip        (t  : Timestamp)        : decodeTimestamp        (encodeTimestamp t)        = .ok t
theorem encodeLeaderPriorities_roundtrip (lp : LeaderPriorities) : decodeLeaderPriorities (encodeLeaderPriorities lp) = .ok lp
theorem encodeSyncOffsets_roundtrip      (so : SyncOffsets)      : decodeSyncOffsets      (encodeSyncOffsets so)      = .ok so
```

## Encoder specification

`Timestamp` and `LeaderPriorities` have only required fields — emit a fixed object:

```
encodeTimestamp t        = .object [("seconds", .number t.seconds), ("nanoseconds", .number t.nanoseconds)]
encodeLeaderPriorities lp = .object [("priority1", .number lp.priority1), ("priority2", .number lp.priority2)]
```

`SyncOffsets` has three optional fields — only include a key when the field is `some`:

```
encodeSyncOffsets so = .object (
  (so.translation.map  fun s => ("translation",  .number s)).toList ++
  (so.rotation.map     fun s => ("rotation",     .number s)).toList ++
  (so.lensEncoders.map fun s => ("lensEncoders", .number s)).toList
)
```

## Proof strategy

- `encodeTimestamp_roundtrip` and `encodeLeaderPriorities_roundtrip`:
  `simp [encodeX, decodeX, JsonValue.lookup?]` on a fixed concrete object.
- `encodeSyncOffsets_roundtrip`: `cases so.translation <;> cases so.rotation <;>
  cases so.lensEncoders` produces 8 concrete list shapes; `simp [encodeSyncOffsets,
  decodeSyncOffsets, JsonValue.lookup?]` closes each.

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No new struct definitions.
- No changes to Slices 1–14.8.

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/LeafEncoders.lean` — exit 0, no warnings.
2. `lake build LeafEncoders` — exit 0.
3. No `sorry` or forbidden constructs.
4. All three roundtrip theorems green.
