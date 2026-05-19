/-
  LensSubEncoders.lean — Slice 15.10A: lens-sub-object-encoders

  Encoders for FizOptions, DistortionOffset, ProjectionOffset, ExposureFalloff,
  and Distortion with roundtrip theorems. Includes infrastructure lemmas
  list_mapM_ok and decodeNonemptyArray_roundtrip (new patterns).

  Ref: docs/laps/encode-decode-roundtrip/15.10A-lens-sub-object-encoders/proof-capsule.md
-/

import Mathlib
import LensDecoder
import TimecodeEncoder

/-─────────────────────────────────────────────────────────────────────────────
  Private copy of decodeNumberString for unfold access.
  decodeDistortion_unfold rewrites decodeDistortion in terms of this local copy
  so that simp can reason about the private function body.
─────────────────────────────────────────────────────────────────────────────-/

private def decodeNumStr (j : JsonValue) : Except DecodeError String :=
  match j with
  | .number s => .ok s
  | _         => .error .expectedNumber

private theorem decodeDistortion_unfold :
    decodeDistortion = fun j =>
      match j with
      | .object _ =>
        match j.lookup? "radial" with
        | none    => .error (.missingField "radial")
        | some rj => do
            let radial     ← decodeNonemptyArray decodeNumStr "radial" rj
            let tangential ← match j.lookup? "tangential" with
                             | none    => .ok none
                             | some tj =>
                               (decodeNonemptyArray decodeNumStr "tangential" tj).map some
            let overscan := match j.lookup? "overscan" with
                            | some (.number s) => some s
                            | _                => none
            let model ← match j.lookup? "model" with
                        | none             => .ok "Brown-Conrady D-U"
                        | some (.string s) => .ok s
                        | some _           => .error .expectedString
            return { radial, tangential, overscan, model }
      | _ => .error .expectedObject := rfl

/-─────────────────────────────────────────────────────────────────────────────
  Infrastructure lemmas
─────────────────────────────────────────────────────────────────────────────-/

private theorem list_mapM_ok
    {α : Type} (enc : α → JsonValue) (dec : JsonValue → Except DecodeError α)
    (hrt : ∀ a, dec (enc a) = .ok a) :
    ∀ xs : List α, (xs.map enc).mapM dec = .ok xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp [List.mapM_cons, hrt hd, ih]
    rfl

private theorem decodeNonemptyArray_roundtrip
    {α : Type} (enc : α → JsonValue) (dec : JsonValue → Except DecodeError α)
    (hrt : ∀ a, dec (enc a) = .ok a) (ctx : String) (arr : NonemptyArray α) :
    decodeNonemptyArray dec ctx (.array (arr.values.map enc)) = .ok arr := by
  obtain ⟨vals, hne⟩ := arr
  rcases List.exists_cons_of_ne_nil hne with ⟨hd, tl, rfl⟩
  simp only [List.map_cons, decodeNonemptyArray,
             show dec (enc hd) = .ok hd from hrt hd,
             show (tl.map enc).mapM dec = .ok tl from list_mapM_ok enc dec hrt tl]
  rfl

/-─────────────────────────────────────────────────────────────────────────────
  Encoders
─────────────────────────────────────────────────────────────────────────────-/

def encodeFizOptions (fiz : FizOptions) : JsonValue :=
  .object (
    (fiz.focus.map fun s => ("focus", .number s)).toList ++
    (fiz.iris.map  fun s => ("iris",  .number s)).toList ++
    (fiz.zoom.map  fun s => ("zoom",  .number s)).toList)

def encodeDistortionOffset (d : DistortionOffset) : JsonValue :=
  .object [("x", .number d.x), ("y", .number d.y)]

def encodeProjectionOffset (p : ProjectionOffset) : JsonValue :=
  .object [("x", .number p.x), ("y", .number p.y)]

def encodeExposureFalloff (ef : ExposureFalloff) : JsonValue :=
  .object (
    [("a1", .number ef.a1)] ++
    (ef.a2.map fun s => ("a2", .number s)).toList ++
    (ef.a3.map fun s => ("a3", .number s)).toList)

def encodeNonemptyStringArray (arr : NonemptyArray String) : JsonValue :=
  .array (arr.values.map .number)

def encodeDistortion (d : Distortion) : JsonValue :=
  .object (
    [("radial", encodeNonemptyStringArray d.radial),
     ("model",  .string d.model)] ++
    (d.tangential.map fun arr => ("tangential", encodeNonemptyStringArray arr)).toList ++
    (d.overscan.map   fun s   => ("overscan",   .number s)).toList)

/-─────────────────────────────────────────────────────────────────────────────
  Roundtrip theorems
─────────────────────────────────────────────────────────────────────────────-/

theorem encodeFizOptions_roundtrip (fiz : FizOptions) :
    decodeFizOptions (encodeFizOptions fiz) = .ok fiz := by
  obtain ⟨fo, ir, zo, hap⟩ := fiz
  rcases fo with _ | fo <;>
  rcases ir with _ | ir <;>
  rcases zo with _ | zo <;>
  simp [encodeFizOptions, decodeFizOptions, JsonValue.lookup?, *]
  simp_all

theorem encodeDistortionOffset_roundtrip (d : DistortionOffset) :
    decodeDistortionOffset (encodeDistortionOffset d) = .ok d := by
  obtain ⟨x, y⟩ := d
  simp [encodeDistortionOffset, decodeDistortionOffset, JsonValue.lookup?]

theorem encodeProjectionOffset_roundtrip (p : ProjectionOffset) :
    decodeProjectionOffset (encodeProjectionOffset p) = .ok p := by
  obtain ⟨x, y⟩ := p
  simp [encodeProjectionOffset, decodeProjectionOffset, JsonValue.lookup?]

theorem encodeExposureFalloff_roundtrip (ef : ExposureFalloff) :
    decodeExposureFalloff (encodeExposureFalloff ef) = .ok ef := by
  obtain ⟨a1, a2, a3⟩ := ef
  rcases a2 with _ | a2 <;>
  rcases a3 with _ | a3 <;>
  simp [encodeExposureFalloff, decodeExposureFalloff, JsonValue.lookup?]

-- Statement uses encodeNonemptyStringArray directly so simp matches before
-- encodeDistortion unfolds it.
private theorem encodeNonemptyStringArray_rt (ctx : String) (arr : NonemptyArray String) :
    decodeNonemptyArray decodeNumStr ctx (encodeNonemptyStringArray arr) = .ok arr :=
  decodeNonemptyArray_roundtrip .number decodeNumStr (fun _ => rfl) ctx arr

theorem encodeDistortion_roundtrip (d : Distortion) :
    decodeDistortion (encodeDistortion d) = .ok d := by
  rw [decodeDistortion_unfold]
  obtain ⟨radial, tangential, overscan, model⟩ := d
  rcases tangential with _ | tan <;>
  rcases overscan with _ | ov <;>
  simp [encodeDistortion, encodeNonemptyStringArray_rt,
        JsonValue.lookup?, Except.map] <;> rfl
