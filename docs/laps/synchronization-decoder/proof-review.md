# Proof Review — synchronization-decoder (Slice 14.6)

## Acceptance criteria

| Criterion | Result |
|---|---|
| `lake env lean opentrackio_parser/SynchronizationDecoder.lean` — exit 0, no warnings | PASS |
| `lake build SynchronizationDecoder` — exit 0 | PASS |
| No `sorry` or forbidden constructs | PASS |

## Review

**Structure**: `decodeSynchronization` follows the standard `do`-block pattern. Two required fields use `←` with `.error` on `none`; four optional fields use `←` + `.map some` or pure `let`.

**Required fields**:
- `locked`: `.bool b` arm; wrong-type arm uses `.error .expectedString` — `DecodeError` has no `expectedBool` variant and Slice 3 is frozen
- `source`: delegated to `decodeSyncSource` (Slice 7 enum decoder)

**Optional fields**:
- `frequency`: `←` + `.map some` via `decodePositiveRational` — can propagate errors
- `offsets`: `←` + `.map some` via `decodeSyncOffsets` (Slice 14.1) — can propagate errors
- `present`: pure `let` via `.bool b` — infallible
- `ptp`: `←` + `.map some` via `decodePtpInfo` (Slice 14.4) — can propagate errors

**No theorems**: consistent with capsule spec.

**Imports**: `TimingEnumDecoders` for `decodeSyncSource`; `RationalDecoder` for `decodePositiveRational`; `LeafDecoders` for `decodeSyncOffsets`; `PtpInfoDecoder` for `decodePtpInfo`.

## Verdict

ACCEPTED. No issues found.
