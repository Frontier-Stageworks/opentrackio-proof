/-
  TimecodeEncoder.lean — Slice 15.6B: timecode-encoder-roundtrip

  Encoders for PositiveRational and Timecode, with roundtrip theorems.
  encodePositiveRational is the foundational rational encoder reused by
  future encoder slices (synchronization, timing, lens, camera).

  Ref: docs/laps/encode-decode-roundtrip/15.6B-timecode-encoder-roundtrip/proof-capsule.md
-/

import Mathlib
import RationalDecoder
import TimecodeDecoder
import NumericLiteralRoundtrip

def encodePositiveRational (r : PositiveRational) : JsonValue :=
  .object [("num",   .number r.num.repr),
           ("denom", .number r.den.repr)]

def encodeTimecode (tc : Timecode) : JsonValue :=
  .object (
    [("hours",     .number tc.hours),
     ("minutes",   .number tc.minutes),
     ("seconds",   .number tc.seconds),
     ("frames",    .number tc.frames),
     ("frameRate", encodePositiveRational tc.frameRate)] ++
    (tc.subFrame.map  fun s => ("subFrame",  .number s)).toList ++
    (tc.dropFrame.map fun b => ("dropFrame", .bool   b)).toList)

theorem encodePositiveRational_roundtrip (r : PositiveRational) :
    decodePositiveRational (encodePositiveRational r) = .ok r := by
  obtain ⟨n, d, hn, hd⟩ := r
  simp [encodePositiveRational, decodePositiveRational, JsonValue.lookup?,
        nat_repr_toNat?_some, hn, hd]

theorem encodeTimecode_roundtrip (tc : Timecode) :
    decodeTimecode (encodeTimecode tc) = .ok tc := by
  obtain ⟨hours, minutes, seconds, frames, frameRate, subFrame, dropFrame⟩ := tc
  obtain ⟨fn, fd, fnp, fdp⟩ := frameRate
  rcases subFrame with _ | sf <;> rcases dropFrame with _ | df <;>
  simp [encodeTimecode, decodeTimecode, encodePositiveRational, decodePositiveRational,
        JsonValue.lookup?, nat_repr_toNat?_some, fnp, fdp] <;>
  rfl
