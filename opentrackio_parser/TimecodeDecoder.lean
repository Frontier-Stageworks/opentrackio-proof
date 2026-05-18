/-
  TimecodeDecoder.lean — Slice 14.5: timecode-decoder

  Decoder for Timecode. Five required fields, two optional.
  frameRate uses decodePositiveRational (Slice 5).
  subFrame and dropFrame are pure let (infallible).
  No theorems.

  Ref: docs/laps/timecode-decoder/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import SampleModel
import RationalDecoder

def decodeTimecode (j : JsonValue) : Except DecodeError Timecode :=
  match j with
  | .object _ => do
      let hours ←
        match j.lookup? "hours" with
        | none             => .error (.missingField "hours")
        | some (.number s) => .ok s
        | some _           => .error .expectedNumber
      let minutes ←
        match j.lookup? "minutes" with
        | none             => .error (.missingField "minutes")
        | some (.number s) => .ok s
        | some _           => .error .expectedNumber
      let seconds ←
        match j.lookup? "seconds" with
        | none             => .error (.missingField "seconds")
        | some (.number s) => .ok s
        | some _           => .error .expectedNumber
      let frames ←
        match j.lookup? "frames" with
        | none             => .error (.missingField "frames")
        | some (.number s) => .ok s
        | some _           => .error .expectedNumber
      let frameRate ←
        match j.lookup? "frameRate" with
        | none    => .error (.missingField "frameRate")
        | some vj => decodePositiveRational vj
      let subFrame :=
        match j.lookup? "subFrame" with
        | some (.number s) => some s
        | _                => none
      let dropFrame :=
        match j.lookup? "dropFrame" with
        | some (.bool b) => some b
        | _              => none
      return { hours, minutes, seconds, frames, frameRate, subFrame, dropFrame }
  | _ => .error .expectedObject
