/-
  CameraDecoder.lean — Slice 9B: camera-decoder

  Decodes a JsonValue into a Camera. All 12 fields are optional; missing fields
  decode to none. The soundness theorem targets captureFrameRate as the
  representative PositiveRational field.

  A4: all static.camera fields optional; missing → none; no defaults.
  A8: normative key names.
  Ref: docs/laps/camera-model-decoder/proof-capsule-9b.md
-/

import Mathlib.Tactic
import DecodeError
import JsonRawModel
import CameraModel
import RationalDecoder

/-─────────────────────────────────────────────────────────────────────────────
  SensorPhysicalDimensions decoder

  Required object; height and width are JSON numbers stored as raw strings.
─────────────────────────────────────────────────────────────────────────────-/

def decodeSensorPhysicalDimensions (j : JsonValue) : Except DecodeError SensorPhysicalDimensions :=
  match j with
  | .object _ =>
    match j.lookup? "height" with
    | none    => .error (.missingField "height")
    | some hj =>
    match j.lookup? "width" with
    | none    => .error (.missingField "width")
    | some wj =>
      match hj, wj with
      | .number hs, .number ws => .ok { height := hs, width := ws }
      | .number _,  _          => .error .expectedNumber
      | _,          _          => .error .expectedNumber
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  SensorResolution decoder

  Required object; height and width are JSON numbers parsed as Nat.
  Bounds ([0, 2147483647]) are deferred.
─────────────────────────────────────────────────────────────────────────────-/

def decodeSensorResolution (j : JsonValue) : Except DecodeError SensorResolution :=
  match j with
  | .object _ =>
    match j.lookup? "height" with
    | none    => .error (.missingField "height")
    | some hj =>
    match j.lookup? "width" with
    | none    => .error (.missingField "width")
    | some wj =>
      match hj, wj with
      | .number hs, .number ws =>
        match hs.toNat?, ws.toNat? with
        | some h, some w => .ok { height := h, width := w }
        | none,   _      => .error (.invalidRational "height")
        | _,      none   => .error (.invalidRational "width")
      | .number _, _ => .error .expectedNumber
      | _,         _ => .error .expectedNumber
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  Optional string field decoder

  Shared helper for the five Option NonemptyString fields. Takes the field
  name (for error messages) and the Option JsonValue from lookup?.
─────────────────────────────────────────────────────────────────────────────-/

def decodeOptionalString (key : String) (jv : Option JsonValue) :
    Except DecodeError (Option NonemptyString) :=
  match jv with
  | none             => .ok none
  | some (.string s) =>
    if h : s ≠ "" then .ok (some ⟨s, h⟩)
    else .error (.missingField key)
  | some _           => .error .expectedString

/-─────────────────────────────────────────────────────────────────────────────
  Camera decoder

  All 12 fields are optional. Uses a do block; absent fields produce none.
─────────────────────────────────────────────────────────────────────────────-/

def decodeCamera (j : JsonValue) : Except DecodeError Camera :=
  match j with
  | .object _ => do
      let captureFrameRate ←
        match j.lookup? "captureFrameRate" with
        | none    => .ok none
        | some vj => (decodePositiveRational vj).map some
      let activeSensorPhysicalDimensions ←
        match j.lookup? "activeSensorPhysicalDimensions" with
        | none    => .ok none
        | some vj => (decodeSensorPhysicalDimensions vj).map some
      let activeSensorResolution ←
        match j.lookup? "activeSensorResolution" with
        | none    => .ok none
        | some vj => (decodeSensorResolution vj).map some
      let make            ← decodeOptionalString "make"            (j.lookup? "make")
      let model           ← decodeOptionalString "model"           (j.lookup? "model")
      let serialNumber    ← decodeOptionalString "serialNumber"    (j.lookup? "serialNumber")
      let firmwareVersion ← decodeOptionalString "firmwareVersion" (j.lookup? "firmwareVersion")
      let label           ← decodeOptionalString "label"           (j.lookup? "label")
      let anamorphicSqueeze ←
        match j.lookup? "anamorphicSqueeze" with
        | none    => .ok none
        | some vj => (decodePositiveRational vj).map some
      let isoSpeed ←
        match j.lookup? "isoSpeed" with
        | none             => .ok none
        | some (.number s) => .ok (some s)
        | some _           => .error (.invalidRational "isoSpeed")
      let fdlLink ←
        match j.lookup? "fdlLink" with
        | none             => .ok none
        | some (.string s) => .ok (some s)
        | some _           => .error .expectedString
      let shutterAngle ←
        match j.lookup? "shutterAngle" with
        | none             => .ok none
        | some (.number s) => .ok (some s)
        | some _           => .error (.invalidRational "shutterAngle")
      return { captureFrameRate, activeSensorPhysicalDimensions, activeSensorResolution,
               make, model, serialNumber, firmwareVersion, label,
               anamorphicSqueeze, isoSpeed, fdlLink, shutterAngle }
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  Soundness theorem

  Any PositiveRational in captureFrameRate satisfies 0 < toReal.
  Proof: positive_rational_toReal_pos r — the decoder hypothesis is unused.
─────────────────────────────────────────────────────────────────────────────-/

theorem decodeCamera_sound
    (j : JsonValue) (c : Camera)
    (_h : decodeCamera j = .ok c) :
    ∀ r, c.captureFrameRate = some r → 0 < r.toReal :=
  fun r _ => positive_rational_toReal_pos r
