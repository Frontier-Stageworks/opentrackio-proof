# Proof Plan — sample-decoder-complete (Slice 14.8)

## File

`opentrackio_parser/SampleDecoder.lean` — modified in place.
No new lakefile entry. `SampleDecoder` is already registered.

---

## Step 1 — Updated imports

Add three new imports after the existing block:

```lean
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
import GlobalStageDecoder
import TrackerDecoder
import TimingDecoder
```

---

## Step 2 — Complete `decodeStaticInfo`

```lean
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
      let stracker ←
        match sj.lookup? "tracker" with
        | none    => .ok none
        | some vj => (decodeStaticTracker vj).map some
      return { duration, camera, lens := slens, tracker := stracker }
  | _ => .error .expectedObject
```

---

## Step 3 — Complete `decodeSample`

```lean
def decodeSample (j : JsonValue) : Except DecodeError Sample :=
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
        | some (.array elems) => (elems.mapM decodeRelatedId).map some
        | some _              => .error .expectedArray
      let staticInfo ←
        match j.lookup? "static" with
        | none    => .ok none
        | some sj => (decodeStaticInfo sj).map some
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
  | _ => .error .expectedObject
```

---

## Step 4 — Existing theorems unchanged

All five theorems (`decodeSample_transforms_sound`, `decodeSample_protocol_sound`,
`decodeSample_lens_encoders_sound`, `decodeSample_static_duration_sound`,
`decodeSample_static_camera_sound`) are copied verbatim. No new theorems.

---

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/SampleDecoder.lean` — exit 0, no warnings.
2. `lake build SampleDecoder` — exit 0.
3. No `sorry` or forbidden constructs.
4. All five existing theorems still compile.
