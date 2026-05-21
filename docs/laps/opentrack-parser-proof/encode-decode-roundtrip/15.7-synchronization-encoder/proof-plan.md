# Proof Plan — synchronization-encoder (Slice 15.7)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/SynchronizationEncoder.lean` | `SynchronizationEncoder` |

Entry appended in `lakefile.toml` after `SynchronizationDecoder`.

---

## Imports

```lean
import Mathlib
import SynchronizationDecoder
import LeafEncoders
import TimecodeEncoder
import PtpInfoEncoder
```

`encodeSyncOffsets` and `encodeSyncOffsets_roundtrip` come from `LeafEncoders` (Slice 15.1).
`encodePositiveRational` / `encodePositiveRational_roundtrip` from `TimecodeEncoder` (15.6B).
`encodePtpInfo` / `encodePtpInfo_roundtrip` from `PtpInfoEncoder` (15.5).

---

## Encoder definition

```lean
def encodeSynchronization (sync : Synchronization) : JsonValue :=
  .object (
    [("locked", .bool sync.locked),
     ("source", .string sync.source.toStr)] ++
    (sync.frequency.map fun r => ("frequency", encodePositiveRational r)).toList ++
    (sync.offsets.map   fun o => ("offsets",   encodeSyncOffsets o)).toList ++
    (sync.present.map   fun b => ("present",   .bool b)).toList ++
    (sync.ptp.map       fun p => ("ptp",       encodePtpInfo p)).toList)
```

---

## Theorem: encodeSynchronization_roundtrip

### Statement

```lean
theorem encodeSynchronization_roundtrip (sync : Synchronization) :
    decodeSynchronization (encodeSynchronization sync) = .ok sync
```

### Proof (VERIFIED via lake env lean --stdin)

```lean
theorem encodeSynchronization_roundtrip (sync : Synchronization) :
    decodeSynchronization (encodeSynchronization sync) = .ok sync := by
  obtain ⟨locked, source, frequency, offsets, present, ptp⟩ := sync
  rcases source <;>
  rcases frequency with _ | fr <;>
  rcases offsets with _ | fo <;>
  rcases present with _ | pr <;>
  rcases ptp with _ | fp <;>
  simp [encodeSynchronization, decodeSynchronization,
        encodePositiveRational_roundtrip, encodeSyncOffsets_roundtrip,
        encodePtpInfo_roundtrip,
        JsonValue.lookup?, SyncSource.toStr, decodeSyncSource,
        Except.map] <;>
  rfl
```

### Why it closes

1. `obtain` — destructures all six `Synchronization` fields.
2. `rcases source` — 4 cases (`genlock`, `videoIn`, `ptp`, `ntp`), making
   `source.toStr` a concrete string so `decodeSyncSource (.string "...")` reduces.
3. `rcases frequency/offsets/present/ptp` — 2 cases each; controls whether the optional
   field is appended to the object, so `lookup?` either finds the field or returns `none`.
4. Total: 4 × 2⁴ = 64 goals.
5. `simp [encodePositiveRational_roundtrip, encodeSyncOffsets_roundtrip, encodePtpInfo_roundtrip]` —
   rewrites nested `decodeFoo (encodeFoo x)` to `.ok x` without expanding the nested
   encoder definitions. This keeps goals small.
6. `simp [Except.map]` — reduces `(.ok x).map some` to `.ok (some x)` for the optional
   fields decoded via `(decodeFoo vj).map some`.
7. `<;> rfl` — closes residual `do`-bind goals of the form
   `(do let y ← Except.ok v; ...) = Except.ok {...}`, which are definitionally true.

---

## Acceptance criteria

1. `lake env lean opentrackio_parser/SynchronizationEncoder.lean` — exit 0, no warnings.
2. `lake build SynchronizationEncoder` — exit 0.
3. `encodeSynchronization_roundtrip` public, no `sorry`.
