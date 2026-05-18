# Proof Review — compose-decoder-soundness / 12B: composed-soundness

## Kernel status

`lake env lean opentrackio_parser/SampleDecoder.lean` — exit 0, no warnings.
`lake build SampleDecoder` — exit 0 (3.2s, 3302 jobs).

## No forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No `open Classical`.
- No new decoders or structs.
- No changes to Slices 1–11.5 or to 12A code.

## No plan deviations

All five theorems match the capsule exactly.

## Theorem audit

| Theorem | Statement | Proof term | `_h` used |
|---|---|---|---|
| `decodeSample_transforms_sound` | `ts.values ≠ []` | `ts.nonempty` | No |
| `decodeSample_protocol_sound` | `ValidVersion p.version` | `protocolVersion_valid p.version` | No |
| `decodeSample_lens_encoders_sound` | `fiz.focus ≠ none ∨ …` | `fiz.anyPresent` | No |
| `decodeSample_static_duration_sound` | `0 < r.toReal` | `positive_rational_toReal_pos r` | No |
| `decodeSample_static_camera_sound` | `0 < r.toReal` | `positive_rational_toReal_pos r` | No |

In every theorem the decoder hypothesis `_h` is unnamed and unused.
Invariants are read directly from struct fields; no `Except.bind` tracing.

## Coverage note

These five theorems cover every invariant-carrying type wired in 12A:
- `NonemptyArray.nonempty` — transforms
- `ValidVersion` via `Fin 10` — protocol
- `FizOptions.anyPresent` — lens encoders
- `PositiveRational` positivity — static duration and static camera captureFrameRate

Raw `String` and `Bool` fields carry no formal invariant.
Deferred fields (`timing`, `tracker`, `globalStage`, `static.tracker`) are `none`
and excluded from the soundness surface.

## Contract compliance

1. ✅ `lake env lean` exit 0, no warnings.
2. ✅ `lake build SampleDecoder` exit 0.
3. ✅ All five theorems check without `sorry`.
4. ✅ No forbidden constructs.
5. ✅ No changes to prior slices.
