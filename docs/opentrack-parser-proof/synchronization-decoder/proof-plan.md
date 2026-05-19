# Proof Plan — synchronization-decoder (Slice 14.6)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/SynchronizationDecoder.lean` | `SynchronizationDecoder` |

Appended after `TimecodeDecoder` in `lakefile.toml`.

---

## Step 1 — Lakefile

```toml
[[lean_lib]]
name = "SynchronizationDecoder"
srcDir = "opentrackio_parser"
```

---

## Step 2 — File header and imports

```lean
/-
  SynchronizationDecoder.lean — Slice 14.6: synchronization-decoder

  Decoder for Synchronization. Two required fields, four optional.
  Uses decodeSyncSource (Slice 7), decodePositiveRational (Slice 5),
  decodeSyncOffsets (Slice 14.1), and decodePtpInfo (Slice 14.4).
  No theorems.

  Ref: docs/laps/synchronization-decoder/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import SampleModel
import TimingEnumDecoders
import RationalDecoder
import LeafDecoders
import PtpInfoDecoder
```

---

## Step 3 — `decodeSynchronization`

```lean
def decodeSynchronization (j : JsonValue) : Except DecodeError Synchronization :=
  match j with
  | .object _ => do
      let locked ←
        match j.lookup? "locked" with
        | none           => .error (.missingField "locked")
        | some (.bool b) => .ok b
        | some _         => .error .expectedString
      let source ←
        match j.lookup? "source" with
        | none    => .error (.missingField "source")
        | some vj => decodeSyncSource vj
      let frequency ←
        match j.lookup? "frequency" with
        | none    => .ok none
        | some vj => (decodePositiveRational vj).map some
      let offsets ←
        match j.lookup? "offsets" with
        | none    => .ok none
        | some vj => (decodeSyncOffsets vj).map some
      let present :=
        match j.lookup? "present" with
        | some (.bool b) => some b
        | _              => none
      let ptp ←
        match j.lookup? "ptp" with
        | none    => .ok none
        | some vj => (decodePtpInfo vj).map some
      return { locked, source, frequency, offsets, present, ptp }
  | _ => .error .expectedObject
```

### Notes

- `locked` is required and uses `.bool b`. Wrong-type arm uses `.error .expectedString` — `DecodeError` has no `expectedBool` variant and Slice 3 is frozen.
- `source` delegates to `decodeSyncSource` which takes a full `JsonValue`.
- `frequency`, `offsets`, and `ptp` use `←` + `.map some` — can propagate errors.
- `present` is pure `let` — `.bool b` pattern, infallible.

---

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/SynchronizationDecoder.lean` — exit 0, no warnings.
2. `lake build SynchronizationDecoder` — exit 0.
3. No `sorry` or forbidden constructs.
