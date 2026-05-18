# Proof Capsule — timing-encoder (Slice 15.8)

## Intent

Define `encodeTiming` and prove `encodeTiming_roundtrip`. All seven Timing fields are
optional, so the encoder is a pure list-append of optional field entries. The roundtrip
proof uses the nested encoder roundtrip lemmas from earlier slices as simp rewrite rules.

## Scope

- One encoder: `encodeTiming`
- One roundtrip theorem: `encodeTiming_roundtrip`
- No decoder changes

## Frozen formal statements

```lean
def encodeTiming (t : Timing) : JsonValue :=
  .object (
    (t.mode.map             fun m  => ("mode",              .string m.toStr)).toList ++
    (t.recordedTimestamp.map fun ts => ("recordedTimestamp", encodeTimestamp ts)).toList ++
    (t.sampleRate.map       fun r  => ("sampleRate",        encodePositiveRational r)).toList ++
    (t.sampleTimestamp.map  fun ts => ("sampleTimestamp",   encodeTimestamp ts)).toList ++
    (t.sequenceNumber.map   fun s  => ("sequenceNumber",    .string s)).toList ++
    (t.synchronization.map  fun s  => ("synchronization",   encodeSynchronization s)).toList ++
    (t.timecode.map         fun tc => ("timecode",           encodeTimecode tc)).toList)

theorem encodeTiming_roundtrip (t : Timing) :
    decodeTiming (encodeTiming t) = .ok t
```

## Why the encoding matches the decoder

`decodeTiming` requires `.object _` and decodes all fields via optional `do`-binds with
`.map some`. The `mode` field uses `decodeTimingMode` (string-literal match), requiring
`mode.toStr` to be concrete. The remaining five decoded-optional fields use nested
roundtrip lemmas. `sequenceNumber` is a pure `let` (infallible), no roundtrip lemma needed.

| Field | Type | Encoder |
|---|---|---|
| `mode` | `Option TimingMode` | `.string m.toStr` |
| `recordedTimestamp` | `Option Timestamp` | `encodeTimestamp ts` |
| `sampleRate` | `Option PositiveRational` | `encodePositiveRational r` |
| `sampleTimestamp` | `Option Timestamp` | `encodeTimestamp ts` |
| `sequenceNumber` | `Option String` | `.string s` (pure let in decoder) |
| `synchronization` | `Option Synchronization` | `encodeSynchronization s` |
| `timecode` | `Option Timecode` | `encodeTimecode tc` |

## Proof strategy

Two-branch split on `mode`:
- `none` branch: 2⁶ = 64 goals (other 6 optional fields)
- `some m` branch: `rcases m` (2 TimingMode values) × 2⁶ = 128 goals

All 192 goals closed by the same `simp` + `<;> rfl`. The `mode=some` branch additionally
needs `TimingMode.toStr` and `decodeTimingMode` in the simp set.

`set_option maxHeartbeats 400000` required (2× default); verified correct at this limit.
Per LAPS stop rule: slow-but-correct is accepted.

## Dependencies

- `TimingDecoder` — `decodeTiming`
- `LeafEncoders` — `encodeTimestamp`, `encodeTimestamp_roundtrip`
- `TimecodeEncoder` — `encodePositiveRational`, `encodePositiveRational_roundtrip`,
  `encodeTimecode`, `encodeTimecode_roundtrip`
- `SynchronizationEncoder` — `encodeSynchronization`, `encodeSynchronization_roundtrip`

## File and lakefile placement

| File | Library name |
|---|---|
| `opentrackio_parser/TimingEncoder.lean` | `TimingEncoder` |

Entry appended in `lakefile.toml` after `TimingDecoder`.

## Stop rules

- Do not change `decodeTiming`
- Do not reduce `maxHeartbeats` below 400000
- If `<;> rfl` fails on any case, stop and report the residual goal
