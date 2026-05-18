/-
  LensDecoder.lean — Slice 10B: lens-decoder

  Decodes a JsonValue into a Lens or StaticLens. The FizOptions.anyPresent
  invariant is constructed locally in decodeFizOptions and is not recovered
  by tracing through the full lens decoder.

  A4: all lens fields optional; distortion.model absent → "Brown-Conrady D-U".
  A8: normative key names.
  Ref: docs/laps/lens-model-decoder/proof-capsule-10b.md
-/

import Mathlib.Tactic
import DecodeError
import JsonRawModel
import LensModel
import NonemptyArrayDecoder

/-─────────────────────────────────────────────────────────────────────────────
  Private helpers
─────────────────────────────────────────────────────────────────────────────-/

private def decodeNumberString (j : JsonValue) : Except DecodeError String :=
  match j with
  | .number s => .ok s
  | _         => .error .expectedNumber

private def decodeOptionalString (key : String) (jv : Option JsonValue) :
    Except DecodeError (Option NonemptyString) :=
  match jv with
  | none             => .ok none
  | some (.string s) =>
    if h : s ≠ "" then .ok (some ⟨s, h⟩)
    else .error (.missingField key)
  | some _           => .error .expectedString

private def decodeCustom (j : JsonValue) : Except DecodeError (List String) :=
  match j with
  | .array elems => elems.mapM (fun ej => match ej with
      | .number s => .ok s
      | _         => .error .expectedNumber)
  | _ => .error .expectedArray

private def decodeCalibrationHistory (j : JsonValue) :
    Except DecodeError (List NonemptyString) :=
  match j with
  | .array elems => elems.mapM (fun ej => match ej with
      | .string s =>
        if h : s ≠ "" then .ok ⟨s, h⟩
        else .error (.missingField "calibrationHistory element")
      | _ => .error .expectedString)
  | _ => .error .expectedArray

/-─────────────────────────────────────────────────────────────────────────────
  FizOptions decoder

  Constructs anyPresent locally via decision proof. If none of focus/iris/zoom
  is present, returns an error. Values are raw JSON number strings.
─────────────────────────────────────────────────────────────────────────────-/

def decodeFizOptions (j : JsonValue) : Except DecodeError FizOptions :=
  match j with
  | .object _ =>
    let focus := match j.lookup? "focus" with
                 | some (.number s) => some s
                 | _                => none
    let iris  := match j.lookup? "iris" with
                 | some (.number s) => some s
                 | _                => none
    let zoom  := match j.lookup? "zoom" with
                 | some (.number s) => some s
                 | _                => none
    if h : focus ≠ none ∨ iris ≠ none ∨ zoom ≠ none then
      .ok { focus, iris, zoom, anyPresent := h }
    else
      .error (.missingField "focus/iris/zoom")
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  DistortionOffset decoder

  Required object; x and y are required JSON numbers.
─────────────────────────────────────────────────────────────────────────────-/

def decodeDistortionOffset (j : JsonValue) : Except DecodeError DistortionOffset :=
  match j with
  | .object _ =>
    match j.lookup? "x" with
    | none    => .error (.missingField "x")
    | some xj =>
    match j.lookup? "y" with
    | none    => .error (.missingField "y")
    | some yj =>
      match xj, yj with
      | .number xs, .number ys => .ok { x := xs, y := ys }
      | .number _,  _          => .error .expectedNumber
      | _,          _          => .error .expectedNumber
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  ProjectionOffset decoder

  Same structure as DistortionOffset.
─────────────────────────────────────────────────────────────────────────────-/

def decodeProjectionOffset (j : JsonValue) : Except DecodeError ProjectionOffset :=
  match j with
  | .object _ =>
    match j.lookup? "x" with
    | none    => .error (.missingField "x")
    | some xj =>
    match j.lookup? "y" with
    | none    => .error (.missingField "y")
    | some yj =>
      match xj, yj with
      | .number xs, .number ys => .ok { x := xs, y := ys }
      | .number _,  _          => .error .expectedNumber
      | _,          _          => .error .expectedNumber
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  ExposureFalloff decoder

  a1 is required; a2 and a3 are optional JSON numbers.
─────────────────────────────────────────────────────────────────────────────-/

def decodeExposureFalloff (j : JsonValue) : Except DecodeError ExposureFalloff :=
  match j with
  | .object _ =>
    match j.lookup? "a1" with
    | none     => .error (.missingField "a1")
    | some a1j =>
      match a1j with
      | .number a1s =>
        let a2 := match j.lookup? "a2" with
                  | some (.number s) => some s
                  | _                => none
        let a3 := match j.lookup? "a3" with
                  | some (.number s) => some s
                  | _                => none
        .ok { a1 := a1s, a2, a3 }
      | _ => .error .expectedNumber
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  Distortion decoder

  radial is required and nonempty. tangential is optional but nonempty if
  present. overscan is an optional number. model defaults to
  "Brown-Conrady D-U" when absent; errors on present non-string.
─────────────────────────────────────────────────────────────────────────────-/

def decodeDistortion (j : JsonValue) : Except DecodeError Distortion :=
  match j with
  | .object _ =>
    match j.lookup? "radial" with
    | none    => .error (.missingField "radial")
    | some rj => do
        let radial     ← decodeNonemptyArray decodeNumberString "radial" rj
        let tangential ← match j.lookup? "tangential" with
                         | none    => .ok none
                         | some tj =>
                           (decodeNonemptyArray decodeNumberString "tangential" tj).map some
        let overscan := match j.lookup? "overscan" with
                        | some (.number s) => some s
                        | _                => none
        let model ← match j.lookup? "model" with
                    | none             => .ok "Brown-Conrady D-U"
                    | some (.string s) => .ok s
                    | some _           => .error .expectedString
        return { radial, tangential, overscan, model }
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  StaticLens decoder

  All 8 fields are optional. Uses do block with inline match on lookup? results.
─────────────────────────────────────────────────────────────────────────────-/

def decodeStaticLens (j : JsonValue) : Except DecodeError StaticLens :=
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
      let make            ← decodeOptionalString "make"            (j.lookup? "make")
      let model           ← decodeOptionalString "model"           (j.lookup? "model")
      let serialNumber    ← decodeOptionalString "serialNumber"    (j.lookup? "serialNumber")
      let firmwareVersion ← decodeOptionalString "firmwareVersion" (j.lookup? "firmwareVersion")
      let nominalFocalLength :=
        match j.lookup? "nominalFocalLength" with
        | some (.number s) => some s
        | _                => none
      let calibrationHistory ← match j.lookup? "calibrationHistory" with
                                | none    => .ok none
                                | some lj => (decodeCalibrationHistory lj).map some
      return { distortionOverscanMax, undistortionOverscanMax, make, model,
               serialNumber, firmwareVersion, nominalFocalLength, calibrationHistory }
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  Lens decoder

  All 12 fields are optional. Uses do block with inline match on lookup? results.
─────────────────────────────────────────────────────────────────────────────-/

def decodeLens (j : JsonValue) : Except DecodeError Lens :=
  match j with
  | .object _ => do
      let custom ← match j.lookup? "custom" with
                   | none    => .ok none
                   | some cj => (decodeCustom cj).map some
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
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  Soundness theorem

  Any FizOptions in lens.encoders satisfies the anyPresent invariant.
  Proof: fiz.anyPresent is the struct field — no decoder tracing needed.
─────────────────────────────────────────────────────────────────────────────-/

theorem decodeLens_sound
    (j : JsonValue) (l : Lens)
    (_h : decodeLens j = .ok l) :
    ∀ fiz, l.encoders = some fiz →
      fiz.focus ≠ none ∨ fiz.iris ≠ none ∨ fiz.zoom ≠ none :=
  fun fiz _ => fiz.anyPresent
