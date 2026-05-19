/-
  SampleEncoder.lean — Slice 15.11: sample-encoder

  Encoders for StaticInfo and Sample with roundtrip theorems.
  Sub-encoder roundtrips imported from prior slices.

  Ref: docs/laps/encode-decode-roundtrip/15.11-sample-encoder/proof-capsule.md
-/

import Mathlib
import SampleDecoder
import VersionEncoder
import GlobalStageEncoder
import TransformEncoder
import TrackerEncoder
import CameraEncoder
import LensEncoder
import TimingEncoder

/-─────────────────────────────────────────────────────────────────────────────
  Local copies of private SampleDecoder helpers
─────────────────────────────────────────────────────────────────────────────-/

private def decodeRelId' (ej : JsonValue) : Except DecodeError String :=
  match ej with
  | .string s => .ok s
  | _         => .error .expectedString

private def decodeStaticInfo' (sj : JsonValue) : Except DecodeError StaticInfo :=
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
      let stracker ←
        match sj.lookup? "tracker" with
        | none    => .ok none
        | some vj => (decodeStaticTracker vj).map some
      return { duration, camera, lens := slens, tracker := stracker }
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  Unfold theorem
─────────────────────────────────────────────────────────────────────────────-/

private theorem decodeSample_unfold :
    decodeSample = fun j =>
      match j with
      | .object _ => do
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
          let relatedSampleIds ←
            match j.lookup? "relatedSampleIds" with
            | none                => .ok none
            | some (.array elems) => (elems.mapM decodeRelId').map some
            | some _              => .error .expectedArray
          let staticInfo ←
            match j.lookup? "static" with
            | none    => .ok none
            | some sj => (decodeStaticInfo' sj).map some
          let globalStage ←
            match j.lookup? "globalStage" with
            | none    => .ok none
            | some vj => (decodeGlobalStage vj).map some
          let timing ←
            match j.lookup? "timing" with
            | none    => .ok none
            | some vj => (decodeTiming vj).map some
          let tracker ←
            match j.lookup? "tracker" with
            | none    => .ok none
            | some vj => (decodeTracker vj).map some
          return { globalStage      := globalStage
                   lens             := lens
                   protocol         := protocol
                   relatedSampleIds := relatedSampleIds
                   sampleId         := sampleId
                   sourceId         := sourceId
                   sourceNumber     := sourceNumber
                   «static»         := staticInfo
                   timing           := timing
                   tracker          := tracker
                   transforms       := transforms }
      | _ => .error .expectedObject := rfl

/-─────────────────────────────────────────────────────────────────────────────
  Infrastructure lemmas (private in LensSubEncoders and LensEncoder; reproved)
─────────────────────────────────────────────────────────────────────────────-/

private theorem list_mapM_ok'
    {α : Type} (enc : α → JsonValue) (dec : JsonValue → Except DecodeError α)
    (hrt : ∀ a, dec (enc a) = .ok a) :
    ∀ xs : List α, (xs.map enc).mapM dec = .ok xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp [List.mapM_cons, hrt hd, ih]
    rfl

private theorem decodeNonemptyArray_roundtrip'
    {α : Type} (enc : α → JsonValue) (dec : JsonValue → Except DecodeError α)
    (hrt : ∀ a, dec (enc a) = .ok a) (ctx : String) (arr : NonemptyArray α) :
    decodeNonemptyArray dec ctx (.array (arr.values.map enc)) = .ok arr := by
  obtain ⟨vals, hne⟩ := arr
  rcases List.exists_cons_of_ne_nil hne with ⟨hd, tl, rfl⟩
  simp only [List.map_cons, decodeNonemptyArray,
             show dec (enc hd) = .ok hd from hrt hd,
             show (tl.map enc).mapM dec = .ok tl from list_mapM_ok' enc dec hrt tl]
  rfl

/-─────────────────────────────────────────────────────────────────────────────
  Helper roundtrip lemmas
─────────────────────────────────────────────────────────────────────────────-/

private theorem encodeRelatedIds_rt (rs : List String) :
    rs.mapM (decodeRelId' ∘ JsonValue.string) = .ok rs := by
  induction rs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.mapM_cons, Function.comp, decodeRelId', ih]
    rfl

private theorem encodeTransformArr_rt (ctx : String) (ta : NonemptyArray Transform) :
    decodeNonemptyArray decodeTransform ctx (.array (ta.values.map encodeTransform)) = .ok ta :=
  decodeNonemptyArray_roundtrip' encodeTransform decodeTransform encodeTransform_roundtrip ctx ta

/-─────────────────────────────────────────────────────────────────────────────
  Encoders
─────────────────────────────────────────────────────────────────────────────-/

private def encodeStaticInfo (si : StaticInfo) : JsonValue :=
  .object (
    (si.duration.map fun r => ("duration", encodePositiveRational r)).toList ++
    (si.camera.map   fun c => ("camera",   encodeCamera c)).toList ++
    (si.lens.map     fun l => ("lens",     encodeStaticLens l)).toList ++
    (si.tracker.map  fun t => ("tracker",  encodeStaticTracker t)).toList)

def encodeSample (s : Sample) : JsonValue :=
  .object (
    (s.globalStage.map      fun g  => ("globalStage",      encodeGlobalStage g)).toList ++
    (s.lens.map             fun l  => ("lens",             encodeLens l)).toList ++
    (s.protocol.map         fun p  => ("protocol",         encodeProtocol p)).toList ++
    (s.relatedSampleIds.map fun rs => ("relatedSampleIds", .array (rs.map .string))).toList ++
    (s.sampleId.map         fun id => ("sampleId",         .string id)).toList ++
    (s.sourceId.map         fun id => ("sourceId",         .string id)).toList ++
    (s.sourceNumber.map     fun n  => ("sourceNumber",     .number n)).toList ++
    (s.«static».map         fun si => ("static",           encodeStaticInfo si)).toList ++
    (s.timing.map           fun t  => ("timing",           encodeTiming t)).toList ++
    (s.tracker.map          fun t  => ("tracker",          encodeTracker t)).toList ++
    (s.transforms.map       fun ta => ("transforms",       .array (ta.values.map encodeTransform))).toList)

/-─────────────────────────────────────────────────────────────────────────────
  Roundtrip theorems
─────────────────────────────────────────────────────────────────────────────-/

private theorem encodeStaticInfo_rt (si : StaticInfo) :
    decodeStaticInfo' (encodeStaticInfo si) = .ok si := by
  obtain ⟨dur, cam, lens, tracker⟩ := si
  rcases dur     with _ | dur     <;>
  rcases cam     with _ | cam     <;>
  rcases lens    with _ | lens    <;>
  rcases tracker with _ | tracker <;>
  simp [encodeStaticInfo, decodeStaticInfo',
        encodePositiveRational_roundtrip,
        encodeCamera_roundtrip,
        encodeStaticLens_roundtrip,
        encodeStaticTracker_roundtrip,
        JsonValue.lookup?, Except.map] <;>
  rfl

set_option maxHeartbeats 40000000

theorem encodeSample_roundtrip (s : Sample) :
    decodeSample (encodeSample s) = .ok s := by
  rw [decodeSample_unfold]
  obtain ⟨gs, lens, proto, rsi, sid, soid, snum, st, tim, trk, xfms⟩ := s
  rcases gs   with _ | gs   <;>
  rcases lens with _ | lens <;>
  rcases proto with _ | proto <;>
  rcases rsi  with _ | rsi  <;>
  rcases st   with _ | st   <;>
  rcases tim  with _ | tim  <;>
  rcases trk  with _ | trk  <;>
  rcases xfms with _ | xfms <;>
  rcases sid  with _ | sid  <;>
  rcases soid with _ | soid <;>
  rcases snum with _ | snum <;>
  simp [encodeSample,
        encodeStaticInfo_rt,
        encodeRelatedIds_rt,
        encodeTransformArr_rt,
        encodeGlobalStage_roundtrip,
        encodeLens_roundtrip,
        encodeProtocol_roundtrip,
        encodeTiming_roundtrip,
        encodeTracker_roundtrip,
        JsonValue.lookup?, Except.map] <;>
  rfl
