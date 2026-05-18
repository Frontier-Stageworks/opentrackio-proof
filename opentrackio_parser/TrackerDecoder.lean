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

private def decodeOptionalString (key : String) (jv : Option JsonValue) :
    Except DecodeError (Option NonemptyString) :=
  match jv with
  | none             => .ok none
  | some (.string s) =>
    if h : s ≠ "" then .ok (some ⟨s, h⟩)
    else .error (.missingField key)
  | some _           => .error .expectedString

def decodeStaticTracker (j : JsonValue) : Except DecodeError StaticTracker :=
  match j with
  | .object _ => do
      let make            ← decodeOptionalString "make"            (j.lookup? "make")
      let model           ← decodeOptionalString "model"           (j.lookup? "model")
      let serialNumber    ← decodeOptionalString "serialNumber"    (j.lookup? "serialNumber")
      let firmwareVersion ← decodeOptionalString "firmwareVersion" (j.lookup? "firmwareVersion")
      return { make, model, serialNumber, firmwareVersion }
  | _ => .error .expectedObject

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
