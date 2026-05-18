/-
  LeafEncoders.lean — Slice 15.1: leaf-encoders

  Encoders for Timestamp, LeaderPriorities, and SyncOffsets,
  with decode-after-encode roundtrip theorems for each.

  Ref: docs/laps/encode-decode-roundtrip/15.1-leaf-encoders/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import SampleModel
import LeafDecoders

def encodeTimestamp (t : Timestamp) : JsonValue :=
  .object [("seconds", .number t.seconds), ("nanoseconds", .number t.nanoseconds)]

def encodeLeaderPriorities (lp : LeaderPriorities) : JsonValue :=
  .object [("priority1", .number lp.priority1), ("priority2", .number lp.priority2)]

def encodeSyncOffsets (so : SyncOffsets) : JsonValue :=
  .object ((so.translation.map  fun s => ("translation",  .number s)).toList ++
           (so.rotation.map     fun s => ("rotation",     .number s)).toList ++
           (so.lensEncoders.map fun s => ("lensEncoders", .number s)).toList)

theorem encodeTimestamp_roundtrip (t : Timestamp) :
    decodeTimestamp (encodeTimestamp t) = .ok t := by
  simp [encodeTimestamp, decodeTimestamp, JsonValue.lookup?]

theorem encodeLeaderPriorities_roundtrip (lp : LeaderPriorities) :
    decodeLeaderPriorities (encodeLeaderPriorities lp) = .ok lp := by
  simp [encodeLeaderPriorities, decodeLeaderPriorities, JsonValue.lookup?]

theorem encodeSyncOffsets_roundtrip (so : SyncOffsets) :
    decodeSyncOffsets (encodeSyncOffsets so) = .ok so := by
  obtain ⟨t, r, l⟩ := so
  cases t <;> cases r <;> cases l <;>
  simp [encodeSyncOffsets, decodeSyncOffsets, JsonValue.lookup?]
