/-
  TrackerEncoder.lean — Slice 15.4: tracker-encoder

  Encoders for StaticTracker and Tracker with roundtrip theorems.
  All NonemptyString fields encoded as .string ns.val; omitted when none.
  Roundtrip proofs use rcases to expose nonemptiness hypotheses for dite reduction.

  Ref: docs/laps/encode-decode-roundtrip/15.4-tracker-encoder/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import TransformModel
import SampleModel
import TrackerDecoder

def encodeStaticTracker (st : StaticTracker) : JsonValue :=
  .object ((st.make.map            fun ns => ("make",            .string ns.val)).toList ++
           (st.model.map           fun ns => ("model",           .string ns.val)).toList ++
           (st.serialNumber.map    fun ns => ("serialNumber",    .string ns.val)).toList ++
           (st.firmwareVersion.map fun ns => ("firmwareVersion", .string ns.val)).toList)

def encodeTracker (t : Tracker) : JsonValue :=
  .object ((t.notes.map     fun ns => ("notes",     .string ns.val)).toList ++
           (t.recording.map fun b  => ("recording", .bool b)).toList         ++
           (t.slate.map     fun ns => ("slate",     .string ns.val)).toList  ++
           (t.status.map    fun ns => ("status",    .string ns.val)).toList)

-- Local copy of TrackerDecoder's private helper; definitionally equal by rfl.
private def decodeOptStr (key : String) (jv : Option JsonValue) :
    Except DecodeError (Option NonemptyString) :=
  match jv with
  | none             => .ok none
  | some (.string s) => if h : s ≠ "" then .ok (some ⟨s, h⟩) else .error (.missingField key)
  | some _           => .error .expectedString

private theorem decodeStaticTracker_unfold :
    decodeStaticTracker = fun j =>
      match j with
      | .object _ => do
          let make            ← decodeOptStr "make"            (j.lookup? "make")
          let model           ← decodeOptStr "model"           (j.lookup? "model")
          let serialNumber    ← decodeOptStr "serialNumber"    (j.lookup? "serialNumber")
          let firmwareVersion ← decodeOptStr "firmwareVersion" (j.lookup? "firmwareVersion")
          return { make, model, serialNumber, firmwareVersion }
      | _ => .error .expectedObject := rfl

private theorem decodeTracker_unfold :
    decodeTracker = fun j =>
      match j with
      | .object _ => do
          let notes     ← decodeOptStr "notes"  (j.lookup? "notes")
          let slate     ← decodeOptStr "slate"  (j.lookup? "slate")
          let status    ← decodeOptStr "status" (j.lookup? "status")
          let recording := match j.lookup? "recording" with
                           | some (.bool b) => some b
                           | _              => none
          return { notes, recording, slate, status }
      | _ => .error .expectedObject := rfl

theorem encodeStaticTracker_roundtrip (st : StaticTracker) :
    decodeStaticTracker (encodeStaticTracker st) = .ok st := by
  rw [decodeStaticTracker_unfold]
  obtain ⟨mk, mo, sn, fv⟩ := st
  rcases mk with _ | ⟨mkv, mkh⟩ <;>
  rcases mo with _ | ⟨mov, moh⟩ <;>
  rcases sn with _ | ⟨snv, snh⟩ <;>
  rcases fv with _ | ⟨fvv, fvh⟩ <;>
  simp [encodeStaticTracker, decodeOptStr, JsonValue.lookup?, *] <;> rfl

theorem encodeTracker_roundtrip (t : Tracker) :
    decodeTracker (encodeTracker t) = .ok t := by
  rw [decodeTracker_unfold]
  obtain ⟨no, re, sl, st⟩ := t
  rcases no with _ | ⟨nov, noh⟩ <;>
  rcases sl with _ | ⟨slv, slh⟩ <;>
  rcases st with _ | ⟨stv, sth⟩ <;>
  cases re <;>
  simp [encodeTracker, decodeOptStr, JsonValue.lookup?, *] <;> rfl
