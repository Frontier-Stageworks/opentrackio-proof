# Proof Capsule — timing-decoder (Slice 14.7)

## Intent

Define `decodeTiming : JsonValue → Except DecodeError Timing`.
All seven fields are optional. Six use `←` + `.map some` (delegating to sub-decoders);
one (`sequenceNumber`) is a pure `let` over a raw string. No theorems.

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/TimingDecoder.lean` | `TimingDecoder` |

One new `[[lean_lib]]` entry appended after `SynchronizationDecoder` in `lakefile.toml`.

## Imports

```lean
import DecodeError
import JsonRawModel
import SampleModel
import TimingEnumDecoders
import RationalDecoder
import LeafDecoders
import TimecodeDecoder
import SynchronizationDecoder
```

## Frozen formal statement

```lean
def decodeTiming (j : JsonValue) : Except DecodeError Timing
```

Accepts a `JsonValue.object`. All fields produce `none` when absent.

## Field specification

| Field | JSON type | Required | Lean type | Decoder |
|---|---|---|---|---|
| `mode` | string (enum) | optional | `Option TimingMode` | `decodeTimingMode`, `←` + `.map some` |
| `recordedTimestamp` | object | optional | `Option Timestamp` | `decodeTimestamp`, `←` + `.map some` |
| `sampleRate` | object | optional | `Option PositiveRational` | `decodePositiveRational`, `←` + `.map some` |
| `sampleTimestamp` | object | optional | `Option Timestamp` | `decodeTimestamp`, `←` + `.map some` |
| `sequenceNumber` | string | optional | `Option String` | `.string s`, pure `let` |
| `synchronization` | object | optional | `Option Synchronization` | `decodeSynchronization`, `←` + `.map some` |
| `timecode` | object | optional | `Option Timecode` | `decodeTimecode`, `←` + `.map some` |

## No theorems

All fields are `Option`; no struct-level invariants.

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No new struct definitions.
- No changes to Slices 1–14.6.

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/TimingDecoder.lean` — exit 0, no warnings.
2. `lake build TimingDecoder` — exit 0.
3. No `sorry` or forbidden constructs.
