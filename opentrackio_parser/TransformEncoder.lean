/-
  TransformEncoder.lean — Slice 15.2: transform-encoder

  Encoders for Vec3, Rotation, and Transform with roundtrip theorems.
  Transform has two optional fields: scale (Option Vec3) and id (Option NonemptyString).
  The id roundtrip discharges the nonemptiness guard via dif_pos ns.nonempty.

  Ref: docs/laps/encode-decode-roundtrip/15.2-transform-encoder/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import TransformModel
import TransformDecoder

def encodeVec3 (v : Vec3) : JsonValue :=
  .object [("x", .number v.x), ("y", .number v.y), ("z", .number v.z)]

def encodeRotation (r : Rotation) : JsonValue :=
  .object [("pan", .number r.pan), ("tilt", .number r.tilt), ("roll", .number r.roll)]

def encodeTransform (t : Transform) : JsonValue :=
  .object ([("translation", encodeVec3 t.translation),
            ("rotation",    encodeRotation t.rotation)] ++
           (t.scale.map fun s  => ("scale", encodeVec3 s)).toList ++
           (t.id.map    fun ns => ("id",    .string ns.val)).toList)

theorem encodeVec3_roundtrip (v : Vec3) :
    decodeVec3 (encodeVec3 v) = .ok v := by
  simp [encodeVec3, decodeVec3, JsonValue.lookup?, decodeNumberField]; rfl

theorem encodeRotation_roundtrip (r : Rotation) :
    decodeRotation (encodeRotation r) = .ok r := by
  simp [encodeRotation, decodeRotation, JsonValue.lookup?, decodeNumberField]; rfl

theorem encodeTransform_roundtrip (t : Transform) :
    decodeTransform (encodeTransform t) = .ok t := by
  obtain ⟨tr, rot, sc, id⟩ := t
  cases sc <;> (cases id with
  | none    =>
    simp [encodeTransform, decodeTransform, JsonValue.lookup?,
          encodeVec3, decodeVec3, decodeNumberField,
          encodeRotation, decodeRotation, decodeIdField]; rfl
  | some ns =>
    obtain ⟨nsval, hns⟩ := ns
    simp [encodeTransform, decodeTransform, JsonValue.lookup?,
          encodeVec3, decodeVec3, decodeNumberField,
          encodeRotation, decodeRotation, decodeIdField,
          dif_pos hns]; rfl)
