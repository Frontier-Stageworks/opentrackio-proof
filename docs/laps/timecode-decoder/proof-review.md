# Proof Review — timecode-decoder (Slice 14.5)

## Acceptance criteria

| Criterion | Result |
|---|---|
| `lake env lean opentrackio_parser/TimecodeDecoder.lean` — exit 0, no warnings | PASS |
| `lake build TimecodeDecoder` — exit 0 | PASS |
| No `sorry` or forbidden constructs | PASS |

## Review

**Structure**: `decodeTimecode` follows the standard `do`-block pattern. Five required fields use `←` with `.error` on `none`; two optional fields use pure `let`.

**Required fields**:
- `hours`, `minutes`, `seconds`, `frames`: raw `.number` strings — consistent with other integer-like fields across the codebase
- `frameRate`: delegated to `decodePositiveRational`, which expects a `.object` with `num`/`denom`

**Optional fields**:
- `subFrame`: pure `let` via `.number s` — infallible
- `dropFrame`: pure `let` via `.bool b` — same pattern as `recording` in TrackerDecoder

**No theorems**: consistent with capsule spec. `PositiveRational` carries its own invariant.

**Imports**: `RationalDecoder` for `decodePositiveRational`; `SampleModel` for `Timecode`/`PositiveRational`.

## Verdict

ACCEPTED. No issues found.
