/-
  LensEncoder.lean — Slice 15.10B: lens-staticlens-lens-encoders

  Encoders for StaticLens and Lens with roundtrip theorems.
  Sub-object encoders imported from LensSubEncoders.

  Ref: docs/laps/encode-decode-roundtrip/15.10B-lens-staticlens-lens-encoders/proof-capsule.md
-/

import Mathlib
import LensDecoder
import LensSubEncoders

/-─────────────────────────────────────────────────────────────────────────────
  Local copies of private LensDecoder helpers
─────────────────────────────────────────────────────────────────────────────-/

private def decodeOptStr (key : String) (jv : Option JsonValue) :
    Except DecodeError (Option NonemptyString) :=
  match jv with
  | none             => .ok none
  | some (.string s) =>
    if h : s ≠ "" then .ok (some ⟨s, h⟩)
    else .error (.missingField key)
  | some _           => .error .expectedString

private def decodeCalHist (j : JsonValue) : Except DecodeError (List NonemptyString) :=
  match j with
  | .array elems => elems.mapM (fun ej => match ej with
      | .string s =>
        if h : s ≠ "" then .ok ⟨s, h⟩
        else .error (.missingField "calibrationHistory element")
      | _ => .error .expectedString)
  | _ => .error .expectedArray

private def decodeCustom' (j : JsonValue) : Except DecodeError (List String) :=
  match j with
  | .array elems => elems.mapM (fun ej => match ej with
      | .number s => .ok s
      | _         => .error .expectedNumber)
  | _ => .error .expectedArray

/-─────────────────────────────────────────────────────────────────────────────
  Unfold theorems
─────────────────────────────────────────────────────────────────────────────-/

private theorem decodeStaticLens_unfold :
    decodeStaticLens = fun j =>
      match j with
      | .object _ => do
          let distortionOverscanMax :=
            match j.lookup? "distortionOverscanMax" with
            | some (.number s) => some s
            | _                => none
          let undistortionOverscanMax :=
            match j.lookup? "undistortionOverscanMax" with
            | some (.number s) => some s
            | _                => none
          let make            ← decodeOptStr "make"            (j.lookup? "make")
          let model           ← decodeOptStr "model"           (j.lookup? "model")
          let serialNumber    ← decodeOptStr "serialNumber"    (j.lookup? "serialNumber")
          let firmwareVersion ← decodeOptStr "firmwareVersion" (j.lookup? "firmwareVersion")
          let nominalFocalLength :=
            match j.lookup? "nominalFocalLength" with
            | some (.number s) => some s
            | _                => none
          let calibrationHistory ← match j.lookup? "calibrationHistory" with
                                    | none    => .ok none
                                    | some lj => (decodeCalHist lj).map some
          return { distortionOverscanMax, undistortionOverscanMax, make, model,
                   serialNumber, firmwareVersion, nominalFocalLength, calibrationHistory }
      | _ => .error .expectedObject := rfl

private theorem decodeLens_unfold :
    decodeLens = fun j =>
      match j with
      | .object _ => do
          let custom ← match j.lookup? "custom" with
                       | none    => .ok none
                       | some cj => (decodeCustom' cj).map some
          let distortion ← match j.lookup? "distortion" with
                           | none    => .ok none
                           | some dj =>
                             (decodeNonemptyArray decodeDistortion "distortion" dj).map some
          let distortionOffset ← match j.lookup? "distortionOffset" with
                                  | none    => .ok none
                                  | some oj => (decodeDistortionOffset oj).map some
          let encoders ← match j.lookup? "encoders" with
                         | none    => .ok none
                         | some ej => (decodeFizOptions ej).map some
          let entrancePupilOffset :=
            match j.lookup? "entrancePupilOffset" with
            | some (.number s) => some s
            | _                => none
          let exposureFalloff ← match j.lookup? "exposureFalloff" with
                                 | none    => .ok none
                                 | some ej => (decodeExposureFalloff ej).map some
          let fStop :=
            match j.lookup? "fStop" with
            | some (.number s) => some s
            | _                => none
          let focusDistance :=
            match j.lookup? "focusDistance" with
            | some (.number s) => some s
            | _                => none
          let pinholeFocalLength :=
            match j.lookup? "pinholeFocalLength" with
            | some (.number s) => some s
            | _                => none
          let projectionOffset ← match j.lookup? "projectionOffset" with
                                  | none    => .ok none
                                  | some oj => (decodeProjectionOffset oj).map some
          let rawEncoders ← match j.lookup? "rawEncoders" with
                            | none    => .ok none
                            | some ej => (decodeFizOptions ej).map some
          let tStop :=
            match j.lookup? "tStop" with
            | some (.number s) => some s
            | _                => none
          return { custom, distortion, distortionOffset, encoders, entrancePupilOffset,
                   exposureFalloff, fStop, focusDistance, pinholeFocalLength,
                   projectionOffset, rawEncoders, tStop }
      | _ => .error .expectedObject := rfl

/-─────────────────────────────────────────────────────────────────────────────
  Infrastructure lemmas (private in LensSubEncoders; reproved locally)
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
  Helper encoders
─────────────────────────────────────────────────────────────────────────────-/

private def encodeCalibrationHistory (hist : List NonemptyString) : JsonValue :=
  .array (hist.map fun ns => .string ns.val)

private def encodeCustom (cs : List String) : JsonValue :=
  .array (cs.map .number)

private def encodeDistortionArray (da : NonemptyArray Distortion) : JsonValue :=
  .array (da.values.map encodeDistortion)

/-─────────────────────────────────────────────────────────────────────────────
  Helper roundtrip lemmas
─────────────────────────────────────────────────────────────────────────────-/

private theorem encodeCalibrationHistory_rt (hist : List NonemptyString) :
    decodeCalHist (encodeCalibrationHistory hist) = .ok hist := by
  simp only [encodeCalibrationHistory, decodeCalHist]
  exact list_mapM_ok'
    (fun ns : NonemptyString => JsonValue.string ns.val)
    (fun ej : JsonValue => match ej with
      | .string s => if h : s ≠ "" then Except.ok (⟨s, h⟩ : NonemptyString)
                    else Except.error (DecodeError.missingField "calibrationHistory element")
      | _ => Except.error DecodeError.expectedString)
    (fun ns => by obtain ⟨v, hv⟩ := ns; simp [dif_pos hv]) hist

private theorem encodeCustom_rt (cs : List String) :
    decodeCustom' (encodeCustom cs) = .ok cs := by
  simp only [encodeCustom, decodeCustom']
  exact list_mapM_ok'
    (fun s : String => JsonValue.number s)
    (fun ej : JsonValue => match ej with
      | .number s => Except.ok s
      | _ => Except.error DecodeError.expectedNumber)
    (fun _ => rfl) cs

private theorem encodeDistortionArray_rt (ctx : String) (da : NonemptyArray Distortion) :
    decodeNonemptyArray decodeDistortion ctx (encodeDistortionArray da) = .ok da :=
  decodeNonemptyArray_roundtrip' encodeDistortion decodeDistortion
    encodeDistortion_roundtrip ctx da

/-─────────────────────────────────────────────────────────────────────────────
  Encoders
─────────────────────────────────────────────────────────────────────────────-/

def encodeStaticLens (sl : StaticLens) : JsonValue :=
  .object (
    (sl.distortionOverscanMax.map   fun s  => ("distortionOverscanMax",   .number s)).toList ++
    (sl.undistortionOverscanMax.map fun s  => ("undistortionOverscanMax", .number s)).toList ++
    (sl.make.map            fun ns => ("make",            .string ns.val)).toList ++
    (sl.model.map           fun ns => ("model",           .string ns.val)).toList ++
    (sl.serialNumber.map    fun ns => ("serialNumber",    .string ns.val)).toList ++
    (sl.firmwareVersion.map fun ns => ("firmwareVersion", .string ns.val)).toList ++
    (sl.nominalFocalLength.map fun s  => ("nominalFocalLength", .number s)).toList ++
    (sl.calibrationHistory.map
      fun hist => ("calibrationHistory", encodeCalibrationHistory hist)).toList)

def encodeLens (l : Lens) : JsonValue :=
  .object (
    (l.custom.map fun cs  => ("custom",              encodeCustom cs)).toList ++
    (l.distortion.map fun da => ("distortion",       encodeDistortionArray da)).toList ++
    (l.distortionOffset.map fun d  => ("distortionOffset", encodeDistortionOffset d)).toList ++
    (l.encoders.map fun fiz => ("encoders",          encodeFizOptions fiz)).toList ++
    (l.entrancePupilOffset.map fun s => ("entrancePupilOffset", .number s)).toList ++
    (l.exposureFalloff.map fun ef => ("exposureFalloff", encodeExposureFalloff ef)).toList ++
    (l.fStop.map fun s         => ("fStop",          .number s)).toList ++
    (l.focusDistance.map fun s => ("focusDistance",  .number s)).toList ++
    (l.pinholeFocalLength.map fun s => ("pinholeFocalLength", .number s)).toList ++
    (l.projectionOffset.map fun p => ("projectionOffset", encodeProjectionOffset p)).toList ++
    (l.rawEncoders.map fun fiz => ("rawEncoders",    encodeFizOptions fiz)).toList ++
    (l.tStop.map fun s         => ("tStop",          .number s)).toList)

/-─────────────────────────────────────────────────────────────────────────────
  Roundtrip theorems
─────────────────────────────────────────────────────────────────────────────-/

set_option maxHeartbeats 10000000

theorem encodeStaticLens_roundtrip (sl : StaticLens) :
    decodeStaticLens (encodeStaticLens sl) = .ok sl := by
  rw [decodeStaticLens_unfold]
  obtain ⟨dom, udom, mk, mdl, sn, fw, nfl, ch⟩ := sl
  rcases mk   with _ | ⟨mkv, mkh⟩ <;>
  rcases mdl  with _ | ⟨mdv, mdh⟩ <;>
  rcases sn   with _ | ⟨snv, snh⟩ <;>
  rcases fw   with _ | ⟨fwv, fwh⟩ <;>
  rcases ch   with _ | ch          <;>
  rcases dom  with _ | dom         <;>
  rcases udom with _ | udom        <;>
  rcases nfl  with _ | nfl         <;>
  simp [encodeStaticLens, decodeOptStr,
        encodeCalibrationHistory_rt, JsonValue.lookup?, Except.map, *] <;>
  rfl

set_option maxHeartbeats 40000000

theorem encodeLens_roundtrip (l : Lens) :
    decodeLens (encodeLens l) = .ok l := by
  rw [decodeLens_unfold]
  obtain ⟨cu, di, doff, enc, epo, ef, fs, fd, pfl, poff, re, ts⟩ := l
  rcases cu   with _ | cu   <;>
  rcases di   with _ | di   <;>
  rcases doff with _ | doff <;>
  rcases enc  with _ | enc  <;>
  rcases ef   with _ | ef   <;>
  rcases poff with _ | poff <;>
  rcases re   with _ | re   <;>
  rcases epo  with _ | epo  <;>
  rcases fs   with _ | fs   <;>
  rcases fd   with _ | fd   <;>
  rcases pfl  with _ | pfl  <;>
  rcases ts   with _ | ts   <;>
  simp [encodeLens,
        encodeCustom_rt, encodeDistortionArray_rt,
        encodeFizOptions_roundtrip,
        encodeDistortionOffset_roundtrip,
        encodeExposureFalloff_roundtrip,
        encodeProjectionOffset_roundtrip,
        JsonValue.lookup?, Except.map] <;>
  rfl
