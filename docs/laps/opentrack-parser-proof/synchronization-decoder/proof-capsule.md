# Proof Capsule — synchronization-decoder (Slice 14.6)

## Intent

Define `decodeSynchronization : JsonValue → Except DecodeError Synchronization`.
Two required fields (`locked` as `Bool`, `source` via `decodeSyncSource`), four optional
fields (`frequency` via `decodePositiveRational`, `offsets` via `decodeSyncOffsets`,
`present` as `Option Bool`, `ptp` via `decodePtpInfo`). No theorems.

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/SynchronizationDecoder.lean` | `SynchronizationDecoder` |

One new `[[lean_lib]]` entry appended after `TimecodeDecoder` in `lakefile.toml`.

## Imports

```lean
import DecodeError
import JsonRawModel
import SampleModel
import TimingEnumDecoders
import RationalDecoder
import LeafDecoders
import PtpInfoDecoder
```

## Frozen formal statement

```lean
def decodeSynchronization (j : JsonValue) : Except DecodeError Synchronization
```

Accepts a `JsonValue.object`. The two required fields produce `.error` when absent.
The four optional fields produce `none` when absent.

## Field specification

| Field | JSON type | Required | Lean type | Decoder |
|---|---|---|---|---|
| `locked` | bool | ✅ | `Bool` | `.bool b`; wrong-type uses `.expectedString` (no `expectedBool` in vocabulary) |
| `source` | string (enum) | ✅ | `SyncSource` | `decodeSyncSource` |
| `frequency` | object | optional | `Option PositiveRational` | `decodePositiveRational`, `←` + `.map some` |
| `offsets` | object | optional | `Option SyncOffsets` | `decodeSyncOffsets`, `←` + `.map some` |
| `present` | bool | optional | `Option Bool` | `.bool b`, pure `let` |
| `ptp` | object | optional | `Option PtpInfo` | `decodePtpInfo`, `←` + `.map some` |

## No theorems

No struct-level invariants beyond what field types carry.

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No new struct definitions.
- No changes to Slices 1–14.5.

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/SynchronizationDecoder.lean` — exit 0, no warnings.
2. `lake build SynchronizationDecoder` — exit 0.
3. No `sorry` or forbidden constructs.
