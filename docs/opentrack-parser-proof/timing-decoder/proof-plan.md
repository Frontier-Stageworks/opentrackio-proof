# Proof Plan — timing-decoder (Slice 14.7)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/TimingDecoder.lean` | `TimingDecoder` |

Appended after `SynchronizationDecoder` in `lakefile.toml`.

---

## Step 1 — Lakefile

```toml
[[lean_lib]]
name = "TimingDecoder"
srcDir = "opentrackio_parser"
```

---

## Step 2 — File header and imports

```lean
/-
  TimingDecoder.lean — Slice 14.7: timing-decoder

  Decoder for Timing. All seven fields are optional.
  Uses decodeTimingMode (Slice 7), decodeTimestamp/decodeSyncOffsets (Slice 14.1),
  decodePositiveRational (Slice 5), decodeTimecode (Slice 14.5),
  and decodeSynchronization (Slice 14.6).
  No theorems.

  Ref: docs/laps/timing-decoder/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import SampleModel
import TimingEnumDecoders
import RationalDecoder
import LeafDecoders
import TimecodeDecoder
import SynchronizationDecoder
```

---

## Step 3 — `decodeTiming`

```lean
def decodeTiming (j : JsonValue) : Except DecodeError Timing :=
  match j with
  | .object _ => do
      let mode ←
        match j.lookup? "mode" with
        | none    => .ok none
        | some vj => (decodeTimingMode vj).map some
      let recordedTimestamp ←
        match j.lookup? "recordedTimestamp" with
        | none    => .ok none
        | some vj => (decodeTimestamp vj).map some
      let sampleRate ←
        match j.lookup? "sampleRate" with
        | none    => .ok none
        | some vj => (decodePositiveRational vj).map some
      let sampleTimestamp ←
        match j.lookup? "sampleTimestamp" with
        | none    => .ok none
        | some vj => (decodeTimestamp vj).map some
      let sequenceNumber :=
        match j.lookup? "sequenceNumber" with
        | some (.string s) => some s
        | _                => none
      let synchronization ←
        match j.lookup? "synchronization" with
        | none    => .ok none
        | some vj => (decodeSynchronization vj).map some
      let timecode ←
        match j.lookup? "timecode" with
        | none    => .ok none
        | some vj => (decodeTimecode vj).map some
      return { mode, recordedTimestamp, sampleRate, sampleTimestamp,
               sequenceNumber, synchronization, timecode }
  | _ => .error .expectedObject
```

### Notes

- All seven fields are optional — no `←` with `.error` anywhere.
- `sequenceNumber` is pure `let` (raw `.string s`, infallible).
- `recordedTimestamp` and `sampleTimestamp` both delegate to `decodeTimestamp`.
- Field order in the `return` struct matches `Timing` declaration order in `SampleModel`.

---

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/TimingDecoder.lean` — exit 0, no warnings.
2. `lake build TimingDecoder` — exit 0.
3. No `sorry` or forbidden constructs.
