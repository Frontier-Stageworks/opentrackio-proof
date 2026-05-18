/-
  SampleDecoder.lean — Slice 12A: decodeSampleShell

  Defines decodeSample : JsonValue → Except DecodeError Sample.
  Wires existing component decoders to Sample fields. Fields with no
  decoder yet produce none. No theorems. No new structs.

  Ref: docs/laps/compose-decoder-soundness/proof-capsule-12a.md
-/

import Mathlib.Tactic
import DecodeError
import JsonRawModel
import RationalDecoder
import NonemptyArrayDecoder
import TransformDecoder
import ProtocolDecoder
import CameraDecoder
import LensDecoder
import SampleModel

private def decodeRelatedId (ej : JsonValue) : Except DecodeError String :=
  match ej with
  | .string s => .ok s
  | _         => .error .expectedString

private def decodeStaticInfo (sj : JsonValue) : Except DecodeError StaticInfo :=
  match sj with
  | .object _ => do
      let duration ←
        match sj.lookup? "duration" with
        | none    => .ok none
        | some vj => (decodePositiveRational vj).map some
      let camera ←
        match sj.lookup? "camera" with
        | none    => .ok none
        | some vj => (decodeCamera vj).map some
      let slens ←
        match sj.lookup? "lens" with
        | none    => .ok none
        | some vj => (decodeStaticLens vj).map some
      return { duration, camera, lens := slens, tracker := none }
  | _ => .error .expectedObject

def decodeSample (j : JsonValue) : Except DecodeError Sample :=
  match j with
  | .object _ => do
      -- Fields wired to existing decoders
      let protocol ←
        match j.lookup? "protocol" with
        | none    => .ok none
        | some vj => (decodeProtocol vj).map some
      let lens ←
        match j.lookup? "lens" with
        | none    => .ok none
        | some vj => (decodeLens vj).map some
      let transforms ←
        match j.lookup? "transforms" with
        | none    => .ok none
        | some vj => (decodeNonemptyArray decodeTransform "transforms" vj).map some
      -- Raw optional string fields
      let sampleId :=
        match j.lookup? "sampleId" with
        | some (.string s) => some s
        | _                => none
      let sourceId :=
        match j.lookup? "sourceId" with
        | some (.string s) => some s
        | _                => none
      let sourceNumber :=
        match j.lookup? "sourceNumber" with
        | some (.number s) => some s
        | _                => none
      -- relatedSampleIds: optional array of strings
      let relatedSampleIds ←
        match j.lookup? "relatedSampleIds" with
        | none                => .ok none
        | some (.array elems) =>
          (elems.mapM decodeRelatedId).map some
        | some _              => .error .expectedArray
      -- static sub-object: decode what we can; tracker deferred
      let staticInfo ←
        match j.lookup? "static" with
        | none    => .ok none
        | some sj => (decodeStaticInfo sj).map some
      -- timing, tracker, globalStage deferred
      return { globalStage      := none
               lens             := lens
               protocol         := protocol
               relatedSampleIds := relatedSampleIds
               sampleId         := sampleId
               sourceId         := sourceId
               sourceNumber     := sourceNumber
               «static»         := staticInfo
               timing           := none
               tracker          := none
               transforms       := transforms }
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  Composed soundness theorems

  All five proofs read a struct field directly. The decoder hypothesis _h
  is unused in every case — invariants live in the types, not in Valid
  predicates, so no Except.bind tracing is required.
─────────────────────────────────────────────────────────────────────────────-/

theorem decodeSample_transforms_sound
    (j : JsonValue) (s : Sample) (_h : decodeSample j = .ok s)
    (ts : NonemptyArray Transform) (_ : s.transforms = some ts) :
    ts.values ≠ [] :=
  ts.nonempty

theorem decodeSample_protocol_sound
    (j : JsonValue) (s : Sample) (_h : decodeSample j = .ok s)
    (p : ProtocolInfo) (_ : s.protocol = some p) :
    ValidVersion p.version :=
  protocolVersion_valid p.version

theorem decodeSample_lens_encoders_sound
    (j : JsonValue) (s : Sample) (_h : decodeSample j = .ok s)
    (l : Lens) (_ : s.lens = some l)
    (fiz : FizOptions) (_ : l.encoders = some fiz) :
    fiz.focus ≠ none ∨ fiz.iris ≠ none ∨ fiz.zoom ≠ none :=
  fiz.anyPresent

theorem decodeSample_static_duration_sound
    (j : JsonValue) (s : Sample) (_h : decodeSample j = .ok s)
    (st : StaticInfo) (_ : s.«static» = some st)
    (r : PositiveRational) (_ : st.duration = some r) :
    0 < r.toReal :=
  positive_rational_toReal_pos r

theorem decodeSample_static_camera_sound
    (j : JsonValue) (s : Sample) (_h : decodeSample j = .ok s)
    (st : StaticInfo) (_ : s.«static» = some st)
    (c : Camera) (_ : st.camera = some c)
    (r : PositiveRational) (_ : c.captureFrameRate = some r) :
    0 < r.toReal :=
  positive_rational_toReal_pos r
