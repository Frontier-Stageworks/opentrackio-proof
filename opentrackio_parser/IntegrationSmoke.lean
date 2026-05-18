/-
  IntegrationSmoke.lean — integration smoke test

  Verifies that all 16 parser modules (Slices 1–11) compose without
  elaboration failure. No new theorems. No sorry. No changes to Slices 1–11.
-/

import RationalValueWrappers
import JsonRawModel
import DecodeError
import ProtocolVersion
import VersionDecoder
import ProtocolDecoder
import RationalDecoder
import NonemptyArrayDecoder
import TimingEnumDecoders
import TransformModel
import TransformDecoder
import CameraModel
import CameraDecoder
import LensModel
import LensDecoder
import SampleModel

-- Component 1: Protocol sub-object; name and version both required.
#eval decodeProtocol (.object [
  ("name",    .string "OpenTrackIO"),
  ("version", .array [.number "1", .number "0", .number "1"])
]) |>.isOk

-- Component 2: Positive rational; num and denom both positive.
#eval decodePositiveRational (.object [
  ("num",   .number "24000"),
  ("denom", .number "1001")
]) |>.isOk

-- Component 3: Transform; translation and rotation required; id optional nonempty string.
#eval decodeTransform (.object [
  ("translation", .object [("x", .number "1"), ("y", .number "0"), ("z", .number "0")]),
  ("rotation",    .object [("pan", .number "0"), ("tilt", .number "0"), ("roll", .number "0")]),
  ("id",          .string "cam1")
]) |>.isOk

-- Component 4: Camera; captureFrameRate carries PositiveRational; make carries NonemptyString.
#eval decodeCamera (.object [
  ("captureFrameRate", .object [("num", .number "24"), ("denom", .number "1")]),
  ("make",             .string "ARRI")
]) |>.isOk

-- Component 5: Lens encoders; FizOptions.anyPresent is satisfied when any of focus/iris/zoom present.
#eval decodeLens (.object [
  ("encoders", .object [
    ("focus", .number "0.5"),
    ("iris",  .number "0.3"),
    ("zoom",  .number "0.1")
  ])
]) |>.isOk

-- Shell construction: decoder outputs threaded into a Sample value.
def smokeSample : Sample :=
  let cOpt := (decodeCamera (.object [("make", .string "ARRI")])).toOption
  let lOpt := (decodeLens (.object [
    ("encoders", .object [
      ("focus", .number "0.5"),
      ("iris",  .number "0.3"),
      ("zoom",  .number "0.1")
    ])
  ])).toOption
  { globalStage      := none
    lens             := lOpt
    protocol         := none
    relatedSampleIds := none
    sampleId         := none
    sourceId         := none
    sourceNumber     := none
    «static»         := cOpt.map (fun c =>
                          { camera   := some c
                            duration := none
                            lens     := none
                            tracker  := none })
    timing           := none
    tracker          := none
    transforms       := none }
