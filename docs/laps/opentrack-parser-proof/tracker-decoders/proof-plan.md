# Proof Plan — tracker-decoders (Slice 14.3)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/TrackerDecoder.lean` | `TrackerDecoder` |

Appended after `GlobalStageDecoder` in `lakefile.toml`.

---

## Step 1 — Lakefile

```toml
[[lean_lib]]
name = "TrackerDecoder"
srcDir = "opentrackio_parser"
```

---

## Step 2 — File header and imports

```lean
/-
  TrackerDecoder.lean — Slice 14.3: tracker-decoders

  Decoders for StaticTracker and Tracker. Optional NonemptyString fields
  use the decodeOptionalString pattern. recording uses JsonValue.bool.
  No theorems.

  Ref: docs/laps/tracker-decoders/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import TransformModel
import SampleModel
```

---

## Step 3 — Private helper

```lean
private def decodeOptionalString (key : String) (jv : Option JsonValue) :
    Except DecodeError (Option NonemptyString) :=
  match jv with
  | none             => .ok none
  | some (.string s) =>
    if h : s ≠ "" then .ok (some ⟨s, h⟩)
    else .error (.missingField key)
  | some _           => .error .expectedString
```

Identical logic to the private helper in `CameraDecoder` and `LensDecoder`.

---

## Step 4 — `decodeStaticTracker`

```lean
def decodeStaticTracker (j : JsonValue) : Except DecodeError StaticTracker :=
  match j with
  | .object _ => do
      let make            ← decodeOptionalString "make"            (j.lookup? "make")
      let model           ← decodeOptionalString "model"           (j.lookup? "model")
      let serialNumber    ← decodeOptionalString "serialNumber"    (j.lookup? "serialNumber")
      let firmwareVersion ← decodeOptionalString "firmwareVersion" (j.lookup? "firmwareVersion")
      return { make, model, serialNumber, firmwareVersion }
  | _ => .error .expectedObject
```

---

## Step 5 — `decodeTracker`

`recording` is a pure `let` (optional bool; absent or wrong-type → `none`).

```lean
def decodeTracker (j : JsonValue) : Except DecodeError Tracker :=
  match j with
  | .object _ => do
      let notes     ← decodeOptionalString "notes"  (j.lookup? "notes")
      let slate     ← decodeOptionalString "slate"  (j.lookup? "slate")
      let status    ← decodeOptionalString "status" (j.lookup? "status")
      let recording := match j.lookup? "recording" with
                       | some (.bool b) => some b
                       | _              => none
      return { notes, recording, slate, status }
  | _ => .error .expectedObject
```

---

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/TrackerDecoder.lean` — exit 0, no warnings.
2. `lake build TrackerDecoder` — exit 0.
3. No `sorry` or forbidden constructs.
