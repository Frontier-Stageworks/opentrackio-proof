/-
  CameraEncoder.lean — Slice 15.9: camera-encoder

  Encoders for SensorPhysicalDimensions, SensorResolution, and Camera
  with roundtrip theorems.
  All 12 Camera fields are optional.
  encodePositiveRational from TimecodeEncoder (15.6B).
  nat_repr_toNat?_some from NumericLiteralRoundtrip (15.6A).

  Ref: docs/laps/encode-decode-roundtrip/15.9-camera-encoder/proof-capsule.md
-/

import Mathlib
import CameraDecoder
import TimecodeEncoder
import NumericLiteralRoundtrip

def encodeSensorPhysicalDimensions (spd : SensorPhysicalDimensions) : JsonValue :=
  .object [("height", .number spd.height),
           ("width",  .number spd.width)]

def encodeSensorResolution (sr : SensorResolution) : JsonValue :=
  .object [("height", .number sr.height.repr),
           ("width",  .number sr.width.repr)]

def encodeCamera (c : Camera) : JsonValue :=
  .object (
    (c.captureFrameRate.map fun r =>
      ("captureFrameRate", encodePositiveRational r)).toList ++
    (c.activeSensorPhysicalDimensions.map fun spd =>
      ("activeSensorPhysicalDimensions", encodeSensorPhysicalDimensions spd)).toList ++
    (c.activeSensorResolution.map fun sr =>
      ("activeSensorResolution", encodeSensorResolution sr)).toList ++
    (c.make.map            fun ns => ("make",            .string ns.val)).toList ++
    (c.model.map           fun ns => ("model",           .string ns.val)).toList ++
    (c.serialNumber.map    fun ns => ("serialNumber",    .string ns.val)).toList ++
    (c.firmwareVersion.map fun ns => ("firmwareVersion", .string ns.val)).toList ++
    (c.label.map           fun ns => ("label",           .string ns.val)).toList ++
    (c.anamorphicSqueeze.map fun r =>
      ("anamorphicSqueeze", encodePositiveRational r)).toList ++
    (c.isoSpeed.map      fun s => ("isoSpeed",    .number s)).toList ++
    (c.fdlLink.map       fun s => ("fdlLink",     .string s)).toList ++
    (c.shutterAngle.map  fun s => ("shutterAngle", .number s)).toList)

theorem encodeSensorPhysicalDimensions_roundtrip (spd : SensorPhysicalDimensions) :
    decodeSensorPhysicalDimensions (encodeSensorPhysicalDimensions spd) = .ok spd := by
  obtain ⟨h, w⟩ := spd
  simp [encodeSensorPhysicalDimensions, decodeSensorPhysicalDimensions, JsonValue.lookup?]

theorem encodeSensorResolution_roundtrip (sr : SensorResolution) :
    decodeSensorResolution (encodeSensorResolution sr) = .ok sr := by
  obtain ⟨h, w⟩ := sr
  simp [encodeSensorResolution, decodeSensorResolution,
        JsonValue.lookup?, nat_repr_toNat?_some]

set_option maxHeartbeats 40000000

theorem encodeCamera_roundtrip (c : Camera) :
    decodeCamera (encodeCamera c) = .ok c := by
  obtain ⟨cfr, aspd, asr, mk, mdl, sn, fw, lbl, as_, iso, fdl, sa⟩ := c
  rcases cfr  with _ | cfr  <;>
  rcases aspd with _ | aspd <;>
  rcases asr  with _ | asr  <;>
  rcases mk   with _ | ⟨mkv, mkh⟩ <;>
  rcases mdl  with _ | ⟨mdv, mdh⟩ <;>
  rcases sn   with _ | ⟨snv, snh⟩ <;>
  rcases fw   with _ | ⟨fwv, fwh⟩ <;>
  rcases lbl  with _ | ⟨lblv, lblh⟩ <;>
  rcases as_  with _ | as_  <;>
  rcases iso  with _ | iso  <;>
  rcases fdl  with _ | fdl  <;>
  rcases sa   with _ | sa   <;>
  simp [encodeCamera, decodeCamera, decodeOptionalString,
        encodeSensorPhysicalDimensions_roundtrip,
        encodeSensorResolution_roundtrip,
        encodePositiveRational_roundtrip,
        JsonValue.lookup?, Except.map, *] <;> rfl
