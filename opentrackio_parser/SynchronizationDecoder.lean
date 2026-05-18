/-
  SynchronizationDecoder.lean — Slice 14.6: synchronization-decoder

  Decoder for Synchronization. Two required fields, four optional.
  Uses decodeSyncSource (Slice 7), decodePositiveRational (Slice 5),
  decodeSyncOffsets (Slice 14.1), and decodePtpInfo (Slice 14.4).
  No theorems.

  Ref: docs/laps/synchronization-decoder/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import SampleModel
import TimingEnumDecoders
import RationalDecoder
import LeafDecoders
import PtpInfoDecoder

def decodeSynchronization (j : JsonValue) : Except DecodeError Synchronization :=
  match j with
  | .object _ => do
      let locked ←
        match j.lookup? "locked" with
        | none           => .error (.missingField "locked")
        | some (.bool b) => .ok b
        | some _         => .error .expectedString
      let source ←
        match j.lookup? "source" with
        | none    => .error (.missingField "source")
        | some vj => decodeSyncSource vj
      let frequency ←
        match j.lookup? "frequency" with
        | none    => .ok none
        | some vj => (decodePositiveRational vj).map some
      let offsets ←
        match j.lookup? "offsets" with
        | none    => .ok none
        | some vj => (decodeSyncOffsets vj).map some
      let present :=
        match j.lookup? "present" with
        | some (.bool b) => some b
        | _              => none
      let ptp ←
        match j.lookup? "ptp" with
        | none    => .ok none
        | some vj => (decodePtpInfo vj).map some
      return { locked, source, frequency, offsets, present, ptp }
  | _ => .error .expectedObject
