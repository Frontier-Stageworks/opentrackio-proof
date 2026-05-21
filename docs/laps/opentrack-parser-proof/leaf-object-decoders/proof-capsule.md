# Proof Capsule — leaf-object-decoders (Slice 14.1)

## Intent

Define decoders for three trivial leaf objects: `Timestamp`, `LeaderPriorities`,
and `SyncOffsets`. All fields are raw strings; no invariant-carrying types are
introduced. No soundness theorems — there is nothing non-trivial to prove.
These decoders are prerequisites for 14.4 (`PtpInfo`) and 14.6 (`Synchronization`).

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/LeafDecoders.lean` | `LeafDecoders` |

One new `[[lean_lib]]` entry appended after `VersionEncoder` in `lakefile.toml`.

## Imports

```lean
import DecodeError
import JsonRawModel
import SampleModel
```

No `Mathlib.Tactic` needed — no proofs.

## Frozen formal statements

### D1 — Timestamp decoder

```lean
def decodeTimestamp (j : JsonValue) : Except DecodeError Timestamp
```

Accepts a `JsonValue.object`. Both `seconds` and `nanoseconds` are required
JSON numbers stored as raw strings.

### D2 — LeaderPriorities decoder

```lean
def decodeLeaderPriorities (j : JsonValue) : Except DecodeError LeaderPriorities
```

Accepts a `JsonValue.object`. Both `priority1` and `priority2` are required
JSON numbers stored as raw strings.

### D3 — SyncOffsets decoder

```lean
def decodeSyncOffsets (j : JsonValue) : Except DecodeError SyncOffsets
```

Accepts a `JsonValue.object`. All three fields (`translation`, `rotation`,
`lensEncoders`) are optional JSON numbers stored as raw strings; absent → `none`.

## Field types (per A4/A8 sample resolution)

| Struct | Field | JSON type | Lean type |
|---|---|---|---|
| `Timestamp` | `seconds` | number (required) | `String` |
| `Timestamp` | `nanoseconds` | number (required) | `String` |
| `LeaderPriorities` | `priority1` | number (required) | `String` |
| `LeaderPriorities` | `priority2` | number (required) | `String` |
| `SyncOffsets` | `translation` | number (optional) | `Option String` |
| `SyncOffsets` | `rotation` | number (optional) | `Option String` |
| `SyncOffsets` | `lensEncoders` | number (optional) | `Option String` |

## No theorems

All fields are raw `String` or `Option String`. No invariant-carrying types
are involved. No soundness theorems in this slice.

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No new struct definitions (all types exist in `SampleModel`).
- No changes to Slices 1–14.

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/LeafDecoders.lean` — exit 0, no warnings.
2. `lake build LeafDecoders` — exit 0.
3. No `sorry` or forbidden constructs.
