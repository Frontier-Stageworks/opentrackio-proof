# Proof Plan — leaf-encoders (Slice 15.1)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/LeafEncoders.lean` | `LeafEncoders` |

Appended after `VersionEncoder` in `lakefile.toml`.

---

## Step 1 — Lakefile

```toml
[[lean_lib]]
name = "LeafEncoders"
srcDir = "opentrackio_parser"
```

---

## Step 2 — File header and imports

```lean
/-
  LeafEncoders.lean — Slice 15.1: leaf-encoders

  Encoders for Timestamp, LeaderPriorities, and SyncOffsets,
  with decode-after-encode roundtrip theorems for each.

  Ref: docs/laps/encode-decode-roundtrip/15.1-leaf-encoders/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import SampleModel
import LeafDecoders
```

---

## Step 3 — Encoders

```lean
def encodeTimestamp (t : Timestamp) : JsonValue :=
  .object [("seconds", .number t.seconds), ("nanoseconds", .number t.nanoseconds)]

def encodeLeaderPriorities (lp : LeaderPriorities) : JsonValue :=
  .object [("priority1", .number lp.priority1), ("priority2", .number lp.priority2)]

def encodeSyncOffsets (so : SyncOffsets) : JsonValue :=
  .object ((so.translation.map  fun s => ("translation",  .number s)).toList ++
           (so.rotation.map     fun s => ("rotation",     .number s)).toList ++
           (so.lensEncoders.map fun s => ("lensEncoders", .number s)).toList)
```

---

## Step 4 — Roundtrip theorems

```lean
theorem encodeTimestamp_roundtrip (t : Timestamp) :
    decodeTimestamp (encodeTimestamp t) = .ok t := by
  simp [encodeTimestamp, decodeTimestamp, JsonValue.lookup?]

theorem encodeLeaderPriorities_roundtrip (lp : LeaderPriorities) :
    decodeLeaderPriorities (encodeLeaderPriorities lp) = .ok lp := by
  simp [encodeLeaderPriorities, decodeLeaderPriorities, JsonValue.lookup?]

theorem encodeSyncOffsets_roundtrip (so : SyncOffsets) :
    decodeSyncOffsets (encodeSyncOffsets so) = .ok so := by
  cases so.translation <;> cases so.rotation <;> cases so.lensEncoders <;>
  simp [encodeSyncOffsets, decodeSyncOffsets, JsonValue.lookup?]
```

### Notes

- `encodeTimestamp` and `encodeLeaderPriorities` produce a fixed-shape object; the
  decoder's sequential `match` on `lookup?` reduces directly via `simp`.
- `encodeSyncOffsets` uses `Option.map ... |>.toList` to omit absent fields. The
  `cases` split produces 8 concrete list shapes, making `simp [JsonValue.lookup?]`
  decidable for each.
- If `simp` alone does not close the `SyncOffsets` goals, try `simp [...]; rfl` or
  `decide` on individual cases.

---

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/LeafEncoders.lean` — exit 0, no warnings.
2. `lake build LeafEncoders` — exit 0.
3. No `sorry` or forbidden constructs.
4. All three roundtrip theorems green.
