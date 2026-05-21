# Proof Plan — leaf-object-decoders (Slice 14.1)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/LeafDecoders.lean` | `LeafDecoders` |

Appended after `VersionEncoder` in `lakefile.toml`.

---

## Step 1 — Lakefile

```toml
[[lean_lib]]
name = "LeafDecoders"
srcDir = "opentrackio_parser"
```

---

## Step 2 — File header and imports

```lean
/-
  LeafDecoders.lean — Slice 14.1: leaf-object-decoders

  Decoders for Timestamp, LeaderPriorities, and SyncOffsets.
  All fields are raw strings; no invariant-carrying types; no theorems.

  Ref: docs/laps/leaf-object-decoders/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import SampleModel
```

---

## Step 3 — `decodeTimestamp`

Both fields are required JSON numbers stored as raw strings.

```lean
def decodeTimestamp (j : JsonValue) : Except DecodeError Timestamp :=
  match j with
  | .object _ =>
    match j.lookup? "seconds" with
    | none               => .error (.missingField "seconds")
    | some (.number s)   =>
      match j.lookup? "nanoseconds" with
      | none               => .error (.missingField "nanoseconds")
      | some (.number ns)  => .ok { seconds := s, nanoseconds := ns }
      | some _             => .error .expectedNumber
    | some _             => .error .expectedNumber
  | _ => .error .expectedObject
```

---

## Step 4 — `decodeLeaderPriorities`

Both fields are required JSON numbers stored as raw strings.

```lean
def decodeLeaderPriorities (j : JsonValue) : Except DecodeError LeaderPriorities :=
  match j with
  | .object _ =>
    match j.lookup? "priority1" with
    | none              => .error (.missingField "priority1")
    | some (.number s)  =>
      match j.lookup? "priority2" with
      | none              => .error (.missingField "priority2")
      | some (.number s2) => .ok { priority1 := s, priority2 := s2 }
      | some _            => .error .expectedNumber
    | some _            => .error .expectedNumber
  | _ => .error .expectedObject
```

---

## Step 5 — `decodeSyncOffsets`

All three fields are optional JSON numbers; absent → `none`.

```lean
def decodeSyncOffsets (j : JsonValue) : Except DecodeError SyncOffsets :=
  match j with
  | .object _ =>
    let translation := match j.lookup? "translation" with
                       | some (.number s) => some s
                       | _                => none
    let rotation    := match j.lookup? "rotation" with
                       | some (.number s) => some s
                       | _                => none
    let lensEncoders := match j.lookup? "lensEncoders" with
                        | some (.number s) => some s
                        | _                => none
    .ok { translation, rotation, lensEncoders }
  | _ => .error .expectedObject
```

---

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/LeafDecoders.lean` — exit 0, no warnings.
2. `lake build LeafDecoders` — exit 0.
3. No `sorry` or forbidden constructs.
