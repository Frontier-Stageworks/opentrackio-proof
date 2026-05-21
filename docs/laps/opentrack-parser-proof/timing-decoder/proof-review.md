# Proof Review — timing-decoder (Slice 14.7)

## Acceptance criteria

| Criterion | Result |
|---|---|
| `lake env lean opentrackio_parser/TimingDecoder.lean` — exit 0, no warnings | PASS |
| `lake build TimingDecoder` — exit 0 | PASS |
| No `sorry` or forbidden constructs | PASS |

## Review

**Structure**: `decodeTiming` is an all-optional `do`-block decoder. No required fields — no `.error (.missingField ...)` anywhere. Six fields use `←` + `.map some`; one uses pure `let`.

**Fields**:
- `mode`: `decodeTimingMode` (Slice 7 enum decoder)
- `recordedTimestamp`, `sampleTimestamp`: both delegate to `decodeTimestamp` (Slice 14.1)
- `sampleRate`: `decodePositiveRational` (Slice 5)
- `sequenceNumber`: pure `let` via `.string s` — infallible
- `synchronization`: `decodeSynchronization` (Slice 14.6)
- `timecode`: `decodeTimecode` (Slice 14.5)

**No theorems**: consistent with capsule spec. All fields are `Option`; no struct-level invariants.

**Imports**: `LeafDecoders` for `decodeTimestamp`; `TimecodeDecoder` and `SynchronizationDecoder` for the two sub-object decoders introduced in this layer.

## Verdict

ACCEPTED. No issues found.
