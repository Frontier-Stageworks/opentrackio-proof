/-
  TimingEncoder.lean — Slice 15.8: timing-encoder

  Encoder for Timing with roundtrip theorem.
  All seven Timing fields are optional.
  encodeTimestamp from LeafEncoders (15.1).
  encodePositiveRational, encodeTimecode from TimecodeEncoder (15.6B).
  encodeSynchronization from SynchronizationEncoder (15.7).

  Ref: docs/laps/encode-decode-roundtrip/15.8-timing-encoder/proof-capsule.md
-/

import Mathlib
import TimingDecoder
import LeafEncoders
import TimecodeEncoder
import SynchronizationEncoder

def encodeTiming (t : Timing) : JsonValue :=
  .object (
    (t.mode.map             fun m  => ("mode",              .string m.toStr)).toList ++
    (t.recordedTimestamp.map fun ts => ("recordedTimestamp", encodeTimestamp ts)).toList ++
    (t.sampleRate.map       fun r  => ("sampleRate",        encodePositiveRational r)).toList ++
    (t.sampleTimestamp.map  fun ts => ("sampleTimestamp",   encodeTimestamp ts)).toList ++
    (t.sequenceNumber.map   fun s  => ("sequenceNumber",    .string s)).toList ++
    (t.synchronization.map  fun s  => ("synchronization",   encodeSynchronization s)).toList ++
    (t.timecode.map         fun tc => ("timecode",           encodeTimecode tc)).toList)

set_option maxHeartbeats 400000

theorem encodeTiming_roundtrip (t : Timing) :
    decodeTiming (encodeTiming t) = .ok t := by
  obtain ⟨mode, rts, sr, sts, sn, sync, tc⟩ := t
  rcases mode with _ | m
  · rcases rts with _ | rts <;> rcases sr with _ | sr <;>
    rcases sts with _ | sts <;> rcases sn with _ | sn <;>
    rcases sync with _ | sync <;> rcases tc with _ | tc <;>
    simp [encodeTiming, decodeTiming,
          encodeTimestamp_roundtrip, encodePositiveRational_roundtrip,
          encodeSynchronization_roundtrip, encodeTimecode_roundtrip,
          JsonValue.lookup?, Except.map] <;> rfl
  · rcases m <;>
    rcases rts with _ | rts <;> rcases sr with _ | sr <;>
    rcases sts with _ | sts <;> rcases sn with _ | sn <;>
    rcases sync with _ | sync <;> rcases tc with _ | tc <;>
    simp [encodeTiming, decodeTiming,
          encodeTimestamp_roundtrip, encodePositiveRational_roundtrip,
          encodeSynchronization_roundtrip, encodeTimecode_roundtrip,
          JsonValue.lookup?, TimingMode.toStr, decodeTimingMode, Except.map] <;> rfl
