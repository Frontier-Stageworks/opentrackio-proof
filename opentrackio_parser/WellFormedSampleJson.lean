/-
  WellFormedSampleJson.lean — Slice 16A: wellformed-predicate

  Defines WellFormedSampleJson : JsonValue → Prop, characterizing the subset of
  JSON inputs that are schema-clean for normalization purposes (Slice 16B).

  A3 policy:
  - NoDupKeys: checked recursively over the whole tree
  - Unknown top-level fields allowed (no allKeysIn on Sample itself)
  - Unknown fields inside schema-defined nested objects rejected
  - Required nested fields asserted present when parent is present
  - No regex/numeric-bound claims beyond existing wrappers

  Ref: docs/laps/encode-decode-roundtrip/16A-wellformed-predicate/proof-capsule.md
-/

import Mathlib
import SampleDecoder

/-─────────────────────────────────────────────────────────────────────────────
  Infrastructure: NoDupKeys (recursive tree predicate)
─────────────────────────────────────────────────────────────────────────────-/

mutual

  private def JsonValue.NoDupKeys (j : JsonValue) : Prop :=
    match j with
    | .object fields =>
        List.Nodup (fields.map Prod.fst) ∧ ndkFields fields
    | .array elems   => ndkArr elems
    | _              => True

  private def ndkFields (fields : List (String × JsonValue)) : Prop :=
    match fields with
    | []       => True
    | p :: ps  => p.2.NoDupKeys ∧ ndkFields ps

  private def ndkArr (elems : List JsonValue) : Prop :=
    match elems with
    | []      => True
    | e :: es => e.NoDupKeys ∧ ndkArr es

end

/-─────────────────────────────────────────────────────────────────────────────
  Infrastructure: allKeysIn
  Holds when every key in an object constructor is in the allowed list.
  Non-object values satisfy it vacuously.
─────────────────────────────────────────────────────────────────────────────-/

private def JsonValue.allKeysIn (j : JsonValue) (allowed : List String) : Prop :=
  match j with
  | .object fields => ∀ p ∈ fields, p.1 ∈ allowed
  | _              => True

/-─────────────────────────────────────────────────────────────────────────────
  Tier-1 predicates — leaf object types (no schema-object sub-fields)
─────────────────────────────────────────────────────────────────────────────-/

private def WellFormedPositiveRational (j : JsonValue) : Prop :=
  j.allKeysIn ["num", "denom"] ∧
  j.hasField "num" ∧ j.hasField "denom"

private def WellFormedGlobalStage (j : JsonValue) : Prop :=
  j.allKeysIn ["E", "N", "U", "lat0", "lon0", "h0"] ∧
  j.hasField "E" ∧ j.hasField "N" ∧ j.hasField "U" ∧
  j.hasField "lat0" ∧ j.hasField "lon0" ∧ j.hasField "h0"

private def WellFormedSensorPhysDims (j : JsonValue) : Prop :=
  j.allKeysIn ["height", "width"] ∧
  j.hasField "height" ∧ j.hasField "width"

private def WellFormedSensorResolution (j : JsonValue) : Prop :=
  j.allKeysIn ["height", "width"] ∧
  j.hasField "height" ∧ j.hasField "width"

private def WellFormedVec3 (j : JsonValue) : Prop :=
  j.allKeysIn ["x", "y", "z"] ∧
  j.hasField "x" ∧ j.hasField "y" ∧ j.hasField "z"

private def WellFormedRotation (j : JsonValue) : Prop :=
  j.allKeysIn ["pan", "tilt", "roll"] ∧
  j.hasField "pan" ∧ j.hasField "tilt" ∧ j.hasField "roll"

private def WellFormedDistortionOffset (j : JsonValue) : Prop :=
  j.allKeysIn ["x", "y"] ∧ j.hasField "x" ∧ j.hasField "y"

private def WellFormedProjectionOffset (j : JsonValue) : Prop :=
  j.allKeysIn ["x", "y"] ∧ j.hasField "x" ∧ j.hasField "y"

private def WellFormedLeaderPriorities (j : JsonValue) : Prop :=
  j.allKeysIn ["priority1", "priority2"] ∧
  j.hasField "priority1" ∧ j.hasField "priority2"

-- All three fields optional; no sub-objects
private def WellFormedSyncOffsets (j : JsonValue) : Prop :=
  j.allKeysIn ["translation", "rotation", "lensEncoders"]

-- All three fields optional numbers; no sub-objects
private def WellFormedFizOptions (j : JsonValue) : Prop :=
  j.allKeysIn ["focus", "iris", "zoom"]

-- All four fields optional nonempty strings; no sub-objects
private def WellFormedStaticTracker (j : JsonValue) : Prop :=
  j.allKeysIn ["make", "model", "serialNumber", "firmwareVersion"]

-- All four fields optional; no sub-objects
private def WellFormedTracker (j : JsonValue) : Prop :=
  j.allKeysIn ["notes", "recording", "slate", "status"]

-- seconds and nanoseconds both required integers (stored as strings); no sub-objects
private def WellFormedTimestamp (j : JsonValue) : Prop :=
  j.allKeysIn ["seconds", "nanoseconds"] ∧
  j.hasField "seconds" ∧ j.hasField "nanoseconds"

-- a1 required; a2 and a3 optional; all numbers (no sub-objects)
private def WellFormedExposureFalloff (j : JsonValue) : Prop :=
  j.allKeysIn ["a1", "a2", "a3"] ∧ j.hasField "a1"

-- radial required; tangential/overscan/model are number arrays or strings (no sub-objects)
private def WellFormedDistortion (j : JsonValue) : Prop :=
  j.allKeysIn ["radial", "tangential", "overscan", "model"] ∧ j.hasField "radial"

-- name and version both required; version is a 3-element number array, not a schema object
private def WellFormedProtocol (j : JsonValue) : Prop :=
  j.allKeysIn ["name", "version"] ∧
  j.hasField "name" ∧ j.hasField "version"

/-─────────────────────────────────────────────────────────────────────────────
  Tier-2 predicates — composite object types (contain schema-object sub-fields)
─────────────────────────────────────────────────────────────────────────────-/

-- All 12 fields optional; captureFrameRate/activeSensorPhysical*/activeSensorResolution
-- carry sub-object predicates
private def WellFormedCamera (j : JsonValue) : Prop :=
  j.allKeysIn ["captureFrameRate", "activeSensorPhysicalDimensions",
               "activeSensorResolution", "make", "model", "serialNumber",
               "firmwareVersion", "label", "anamorphicSqueeze", "isoSpeed",
               "fdlLink", "shutterAngle"] ∧
  (∀ vj, j.lookup? "captureFrameRate"               = some vj → WellFormedPositiveRational vj) ∧
  (∀ vj, j.lookup? "activeSensorPhysicalDimensions" = some vj → WellFormedSensorPhysDims vj) ∧
  (∀ vj, j.lookup? "activeSensorResolution"         = some vj → WellFormedSensorResolution vj)

-- All 8 fields optional; calibrationHistory is a string array, not a schema object
private def WellFormedStaticLens (j : JsonValue) : Prop :=
  j.allKeysIn ["distortionOverscanMax", "undistortionOverscanMax",
               "make", "model", "serialNumber", "firmwareVersion",
               "nominalFocalLength", "calibrationHistory"]

-- All 4 fields optional; sub-objects carry their own predicates
private def WellFormedStaticInfo (j : JsonValue) : Prop :=
  j.allKeysIn ["duration", "camera", "lens", "tracker"] ∧
  (∀ vj, j.lookup? "duration" = some vj → WellFormedPositiveRational vj) ∧
  (∀ vj, j.lookup? "camera"   = some vj → WellFormedCamera vj) ∧
  (∀ vj, j.lookup? "lens"     = some vj → WellFormedStaticLens vj) ∧
  (∀ vj, j.lookup? "tracker"  = some vj → WellFormedStaticTracker vj)

-- translation and rotation required; id (optional string) and scale (optional number) not sub-objects
private def WellFormedTransform (j : JsonValue) : Prop :=
  j.allKeysIn ["id", "translation", "rotation", "scale"] ∧
  j.hasField "translation" ∧ j.hasField "rotation" ∧
  (∀ vj, j.lookup? "translation" = some vj → WellFormedVec3 vj) ∧
  (∀ vj, j.lookup? "rotation"    = some vj → WellFormedRotation vj)

-- First 6 fields required; leaderTimeSource and vlan optional
private def WellFormedPtpInfo (j : JsonValue) : Prop :=
  j.allKeysIn ["profile", "domain", "leaderIdentity", "leaderPriorities",
               "leaderAccuracy", "meanPathDelay", "leaderTimeSource", "vlan"] ∧
  j.hasField "profile" ∧ j.hasField "domain" ∧ j.hasField "leaderIdentity" ∧
  j.hasField "leaderPriorities" ∧ j.hasField "leaderAccuracy" ∧ j.hasField "meanPathDelay" ∧
  (∀ vj, j.lookup? "leaderPriorities" = some vj → WellFormedLeaderPriorities vj)

-- locked and source required; others optional
private def WellFormedSynchronization (j : JsonValue) : Prop :=
  j.allKeysIn ["locked", "source", "frequency", "offsets", "present", "ptp"] ∧
  j.hasField "locked" ∧ j.hasField "source" ∧
  (∀ vj, j.lookup? "frequency" = some vj → WellFormedPositiveRational vj) ∧
  (∀ vj, j.lookup? "offsets"   = some vj → WellFormedSyncOffsets vj) ∧
  (∀ vj, j.lookup? "ptp"       = some vj → WellFormedPtpInfo vj)

-- First 5 fields required; subFrame and dropFrame optional
private def WellFormedTimecode (j : JsonValue) : Prop :=
  j.allKeysIn ["hours", "minutes", "seconds", "frames", "frameRate", "subFrame", "dropFrame"] ∧
  j.hasField "hours" ∧ j.hasField "minutes" ∧ j.hasField "seconds" ∧
  j.hasField "frames" ∧ j.hasField "frameRate" ∧
  (∀ vj, j.lookup? "frameRate" = some vj → WellFormedPositiveRational vj)

-- distortion is a NonemptyArray; WellFormedDistortion checked per element
private def WellFormedLens (j : JsonValue) : Prop :=
  j.allKeysIn ["custom", "distortion", "distortionOffset", "encoders",
               "entrancePupilOffset", "exposureFalloff", "fStop", "focusDistance",
               "pinholeFocalLength", "projectionOffset", "rawEncoders", "tStop"] ∧
  (∀ vj, j.lookup? "distortionOffset" = some vj → WellFormedDistortionOffset vj) ∧
  (∀ vj, j.lookup? "encoders"         = some vj → WellFormedFizOptions vj) ∧
  (∀ vj, j.lookup? "rawEncoders"      = some vj → WellFormedFizOptions vj) ∧
  (∀ vj, j.lookup? "exposureFalloff"  = some vj → WellFormedExposureFalloff vj) ∧
  (∀ vj, j.lookup? "projectionOffset" = some vj → WellFormedProjectionOffset vj) ∧
  (∀ arr, j.lookup? "distortion" = some (.array arr) → ∀ e ∈ arr, WellFormedDistortion e)

-- All 7 fields optional
private def WellFormedTiming (j : JsonValue) : Prop :=
  j.allKeysIn ["mode", "recordedTimestamp", "sampleRate", "sampleTimestamp",
               "sequenceNumber", "synchronization", "timecode"] ∧
  (∀ vj, j.lookup? "recordedTimestamp" = some vj → WellFormedTimestamp vj) ∧
  (∀ vj, j.lookup? "sampleTimestamp"   = some vj → WellFormedTimestamp vj) ∧
  (∀ vj, j.lookup? "sampleRate"        = some vj → WellFormedPositiveRational vj) ∧
  (∀ vj, j.lookup? "synchronization"   = some vj → WellFormedSynchronization vj) ∧
  (∀ vj, j.lookup? "timecode"          = some vj → WellFormedTimecode vj)

/-─────────────────────────────────────────────────────────────────────────────
  WellFormedSampleJson
─────────────────────────────────────────────────────────────────────────────-/

-- NoDupKeys checked recursively at the root (covers all descendants).
-- No allKeysIn on j itself — Sample is extension-tolerant per A3.
-- relatedSampleIds is an array of plain strings; no schema-object sub-predicate.
-- sampleId, sourceId, sourceNumber are scalars; no sub-predicate.
def WellFormedSampleJson (j : JsonValue) : Prop :=
  j.NoDupKeys ∧
  (∀ vj, j.lookup? "globalStage" = some vj → WellFormedGlobalStage vj) ∧
  (∀ vj, j.lookup? "lens"        = some vj → WellFormedLens vj) ∧
  (∀ vj, j.lookup? "protocol"    = some vj → WellFormedProtocol vj) ∧
  (∀ vj, j.lookup? "static"      = some vj → WellFormedStaticInfo vj) ∧
  (∀ vj, j.lookup? "timing"      = some vj → WellFormedTiming vj) ∧
  (∀ vj, j.lookup? "tracker"     = some vj → WellFormedTracker vj) ∧
  (∀ arr, j.lookup? "transforms" = some (.array arr) → ∀ e ∈ arr, WellFormedTransform e)
