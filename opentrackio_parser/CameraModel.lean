/-
  CameraModel.lean — Slice 9A: camera-model

  Defines the Camera data model for the OpenTrackIO static.camera sub-tree.
  All fields are Option per A4 (all described fields are optional for consumers).
  No decoder. No theorems.

  A4: missing fields → none; no schema defaults.
  A8: normative key names for all 12 fields.
  Ref: docs/laps/camera-model-decoder/proof-capsule-9a.md
-/

import RationalValueWrappers
import TransformModel

/-─────────────────────────────────────────────────────────────────────────────
  SensorPhysicalDimensions

  Height and width as raw JSON number strings (minimum 0.0; bounds deferred).
─────────────────────────────────────────────────────────────────────────────-/

structure SensorPhysicalDimensions where
  height : String
  width  : String

/-─────────────────────────────────────────────────────────────────────────────
  SensorResolution

  Height and width as natural numbers (integer [0, 2147483647]; bounds deferred).
─────────────────────────────────────────────────────────────────────────────-/

structure SensorResolution where
  height : Nat
  width  : Nat

/-─────────────────────────────────────────────────────────────────────────────
  Camera

  All 12 fields are Option. Invariants are carried by the field types:
  PositiveRational for rational fields, NonemptyString for string-identity
  fields, plain String or Nat for the rest.
─────────────────────────────────────────────────────────────────────────────-/

structure Camera where
  captureFrameRate               : Option PositiveRational
  activeSensorPhysicalDimensions : Option SensorPhysicalDimensions
  activeSensorResolution         : Option SensorResolution
  make                           : Option NonemptyString
  model                          : Option NonemptyString
  serialNumber                   : Option NonemptyString
  firmwareVersion                : Option NonemptyString
  label                          : Option NonemptyString
  anamorphicSqueeze              : Option PositiveRational
  isoSpeed                       : Option String
  fdlLink                        : Option String
  shutterAngle                   : Option String
