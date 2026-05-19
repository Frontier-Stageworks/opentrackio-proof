# Proof Plan — timecode-decoder (Slice 14.5)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/TimecodeDecoder.lean` | `TimecodeDecoder` |

Appended after `PtpInfoDecoder` in `lakefile.toml`.

---

## Step 1 — Lakefile

```toml
[[lean_lib]]
name = "TimecodeDecoder"
srcDir = "opentrackio_parser"
```

---

## Step 2 — File header and imports

```lean
/-
  TimecodeDecoder.lean — Slice 14.5: timecode-decoder

  Decoder for Timecode. Five required fields, two optional.
  frameRate uses decodePositiveRational (Slice 5).
  subFrame and dropFrame are pure let (infallible).
  No theorems.

  Ref: docs/laps/timecode-decoder/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import SampleModel
import RationalDecoder
```

---

## Step 3 — `decodeTimecode`

```lean
def decodeTimecode (j : JsonValue) : Except DecodeError Timecode :=
  match j with
  | .object _ => do
      let hours ←
        match j.lookup? "hours" with
        | none             => .error (.missingField "hours")
        | some (.number s) => .ok s
        | some _           => .error .expectedNumber
      let minutes ←
        match j.lookup? "minutes" with
        | none             => .error (.missingField "minutes")
        | some (.number s) => .ok s
        | some _           => .error .expectedNumber
      let seconds ←
        match j.lookup? "seconds" with
        | none             => .error (.missingField "seconds")
        | some (.number s) => .ok s
        | some _           => .error .expectedNumber
      let frames ←
        match j.lookup? "frames" with
        | none             => .error (.missingField "frames")
        | some (.number s) => .ok s
        | some _           => .error .expectedNumber
      let frameRate ←
        match j.lookup? "frameRate" with
        | none    => .error (.missingField "frameRate")
        | some vj => decodePositiveRational vj
      let subFrame :=
        match j.lookup? "subFrame" with
        | some (.number s) => some s
        | _                => none
      let dropFrame :=
        match j.lookup? "dropFrame" with
        | some (.bool b) => some b
        | _              => none
      return { hours, minutes, seconds, frames, frameRate, subFrame, dropFrame }
  | _ => .error .expectedObject
```

### Notes

- `hours`, `minutes`, `seconds`, `frames` are raw `.number` strings — same pattern as `domain`/`leaderAccuracy` in PtpInfoDecoder.
- `frameRate` delegates to `decodePositiveRational` which takes a full `JsonValue` (expects `.object` with `num`/`denom`).
- `subFrame` and `dropFrame` are pure `let` (no `←`) — cannot fail.
- `dropFrame` uses `.bool b` — same pattern as `recording` in TrackerDecoder.

---

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/TimecodeDecoder.lean` — exit 0, no warnings.
2. `lake build TimecodeDecoder` — exit 0.
3. No `sorry` or forbidden constructs.
