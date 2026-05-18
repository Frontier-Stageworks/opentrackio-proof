# Proof Plan — timing-encoder (Slice 15.8)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/TimingEncoder.lean` | `TimingEncoder` |

Entry appended in `lakefile.toml` after `TimingDecoder`.

---

## Imports

```lean
import Mathlib
import TimingDecoder
import LeafEncoders
import TimecodeEncoder
import SynchronizationEncoder
```

`encodeTimestamp` / `encodeTimestamp_roundtrip` from `LeafEncoders` (15.1).
`encodePositiveRational` / `encodePositiveRational_roundtrip`, `encodeTimecode` /
`encodeTimecode_roundtrip` from `TimecodeEncoder` (15.6B).
`encodeSynchronization` / `encodeSynchronization_roundtrip` from `SynchronizationEncoder` (15.7).

---

## Encoder definition

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
```

---

## Theorem: encodeTiming_roundtrip

### Statement

```lean
theorem encodeTiming_roundtrip (t : Timing) :
    decodeTiming (encodeTiming t) = .ok t
```

### Proof (VERIFIED via lake env lean --stdin at 400000 heartbeats)

```lean
set_option maxHeartbeats 400000

theorem encodeTiming_roundtrip (t : Timing) :
    decodeTiming (encodeTiming t) = .ok t := by
  obtain ⟨mode, rts, sr, sts, sn, sync, tc⟩ := t
  rcases mode with _ | m
  · rcases rts with _ | rts <;> rcases sr with _ | sr <;>
    rcases sts with _ | sts <;> rcases sn with _ | sn <;>
    rcases sync with _ | sync <;> rcases tc with _ | tc <;>
    simp [encodeTiming, decodeTiming,
          encodeTimestamp_roundtrip, encodePositiveRational_roundtrip,
          encodeSynchronization_roundtrip, encodeTimecode_roundtrip,
          JsonValue.lookup?, Except.map] <;> rfl
  · rcases m <;>
    rcases rts with _ | rts <;> rcases sr with _ | sr <;>
    rcases sts with _ | sts <;> rcases sn with _ | sn <;>
    rcases sync with _ | sync <;> rcases tc with _ | tc <;>
    simp [encodeTiming, decodeTiming,
          encodeTimestamp_roundtrip, encodePositiveRational_roundtrip,
          encodeSynchronization_roundtrip, encodeTimecode_roundtrip,
          JsonValue.lookup?, TimingMode.toStr, decodeTimingMode, Except.map] <;> rfl
```

### Why it closes

1. `obtain` — destructures all seven `Timing` fields.

2. Two-branch split on `mode`:
   - `none` branch: no `mode` field in the encoded object; `lookup? "mode" = none → .ok none`.
   - `some m` branch: `rcases m` splits into `.internal` and `.external`, making `m.toStr`
     a concrete string so `decodeTimingMode (.string "internal" / "external")` reduces.

3. `rcases` on the remaining six optional fields — 2⁶ = 64 sub-goals per `mode` branch.
   Total: 64 + 2 × 64 = **192 goals**.

4. `simp [encodeTiming, decodeTiming]` — unfolds encoder (concrete object field list) and
   decoder (`do` block with `lookup?` calls).

5. `simp [encodeTimestamp_roundtrip, encodePositiveRational_roundtrip,
          encodeSynchronization_roundtrip, encodeTimecode_roundtrip]` — rewrites each
   `decodeFoo (encodeFoo x)` sub-term to `.ok x` before the nested encoder is expanded.
   This keeps goals small; nested encoder internals are never exposed.

6. `simp [Except.map]` — reduces `(.ok x).map some` to `.ok (some x)` for every optional
   field decoded via `(decodeFoo vj).map some`.

7. `<;> rfl` — closes residual `do`-bind goals of the form
   `(do let y ← Except.ok v; ...) = Except.ok {...}` (definitionally true).

8. `mode=none` branch omits `TimingMode.toStr` and `decodeTimingMode` from the simp set
   (unused there); `mode=some` branch adds both.

### Heartbeat note

Default 200000 heartbeats times out on the `some m` branch (128 goals × simp cost).
`set_option maxHeartbeats 400000` (2× default) is sufficient and verified. Per LAPS
capsule stop rule: slow-but-correct is accepted.

---

## Acceptance criteria

1. `lake env lean opentrackio_parser/TimingEncoder.lean` — exit 0, no warnings.
2. `lake build TimingEncoder` — exit 0.
3. `encodeTiming_roundtrip` public, no `sorry`.
