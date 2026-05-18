/-
  SynchronizationEncoder.lean — Slice 15.7: synchronization-encoder

  Encoder for Synchronization with roundtrip theorem.
  encodeSyncOffsets is imported from LeafEncoders (Slice 15.1).
  encodePositiveRational from TimecodeEncoder (15.6B).
  encodePtpInfo from PtpInfoEncoder (15.5).

  Ref: docs/laps/encode-decode-roundtrip/15.7-synchronization-encoder/proof-capsule.md
-/

import Mathlib
import SynchronizationDecoder
import LeafEncoders
import TimecodeEncoder
import PtpInfoEncoder

def encodeSynchronization (sync : Synchronization) : JsonValue :=
  .object (
    [("locked", .bool sync.locked),
     ("source", .string sync.source.toStr)] ++
    (sync.frequency.map fun r => ("frequency", encodePositiveRational r)).toList ++
    (sync.offsets.map   fun o => ("offsets",   encodeSyncOffsets o)).toList ++
    (sync.present.map   fun b => ("present",   .bool b)).toList ++
    (sync.ptp.map       fun p => ("ptp",       encodePtpInfo p)).toList)

theorem encodeSynchronization_roundtrip (sync : Synchronization) :
    decodeSynchronization (encodeSynchronization sync) = .ok sync := by
  obtain ⟨locked, source, frequency, offsets, present, ptp⟩ := sync
  rcases source <;>
  rcases frequency with _ | fr <;>
  rcases offsets with _ | fo <;>
  rcases present with _ | pr <;>
  rcases ptp with _ | fp <;>
  simp [encodeSynchronization, decodeSynchronization,
        encodePositiveRational_roundtrip, encodeSyncOffsets_roundtrip,
        encodePtpInfo_roundtrip,
        JsonValue.lookup?, SyncSource.toStr, decodeSyncSource,
        Except.map] <;>
  rfl
