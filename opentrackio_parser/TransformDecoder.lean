/-
  TransformDecoder.lean — Slice 8B: transform-decoder

  Decodes a JsonValue into a Transform. The id-nonemptiness invariant is
  carried by NonemptyString; the soundness proof does not trace Except binds.

  A9: rotation is Euler pan/tilt/roll in degrees. No angle bounds.
  Ref: docs/laps/transform-decoder/proof-capsule-8b.md
-/

import Mathlib.Tactic
import DecodeError
import JsonRawModel
import TransformModel

/-─────────────────────────────────────────────────────────────────────────────
  Helper: required numeric field

  Accepts JsonValue.number; rejects anything else.
─────────────────────────────────────────────────────────────────────────────-/

def decodeNumberField (ctx : String) (j : JsonValue) : Except DecodeError String :=
  match j with
  | .number s => .ok s
  | _         => .error (.invalidRational ctx)

/-─────────────────────────────────────────────────────────────────────────────
  Vec3 decoder

  Required object with "x", "y", "z" number fields.
─────────────────────────────────────────────────────────────────────────────-/

def decodeVec3 (j : JsonValue) : Except DecodeError Vec3 :=
  match j with
  | .object _ =>
    match j.lookup? "x" with
    | none    => .error (.missingField "x")
    | some xj =>
    match j.lookup? "y" with
    | none    => .error (.missingField "y")
    | some yj =>
    match j.lookup? "z" with
    | none    => .error (.missingField "z")
    | some zj => do
        let x ← decodeNumberField "x" xj
        let y ← decodeNumberField "y" yj
        let z ← decodeNumberField "z" zj
        return { x, y, z }
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  Rotation decoder

  Required object with "pan", "tilt", "roll" number fields.
  Angles are unbounded; no range check.
─────────────────────────────────────────────────────────────────────────────-/

def decodeRotation (j : JsonValue) : Except DecodeError Rotation :=
  match j with
  | .object _ =>
    match j.lookup? "pan" with
    | none    => .error (.missingField "pan")
    | some pj =>
    match j.lookup? "tilt" with
    | none    => .error (.missingField "tilt")
    | some tj =>
    match j.lookup? "roll" with
    | none    => .error (.missingField "roll")
    | some rj => do
        let pan  ← decodeNumberField "pan"  pj
        let tilt ← decodeNumberField "tilt" tj
        let roll ← decodeNumberField "roll" rj
        return { pan, tilt, roll }
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  Id field decoder

  Looks up "id" on j. If absent: none. If present and a nonempty string:
  some ⟨s, h⟩. Rejects empty strings and non-string values.
─────────────────────────────────────────────────────────────────────────────-/

def decodeIdField (j : JsonValue) : Except DecodeError (Option NonemptyString) :=
  match j.lookup? "id" with
  | none    => .ok none
  | some ij =>
    match ij with
    | .string s =>
      if h : s ≠ "" then .ok (some ⟨s, h⟩)
      else .error (.missingField "id")
    | _ => .error .expectedString

/-─────────────────────────────────────────────────────────────────────────────
  Transform decoder

  Required "translation" and "rotation" sub-objects; optional "scale" and "id".
─────────────────────────────────────────────────────────────────────────────-/

def decodeTransform (j : JsonValue) : Except DecodeError Transform :=
  match j with
  | .object _ =>
    match j.lookup? "translation" with
    | none    => .error (.missingField "translation")
    | some tj =>
    match j.lookup? "rotation" with
    | none    => .error (.missingField "rotation")
    | some rj => do
        let translation ← decodeVec3 tj
        let rotation    ← decodeRotation rj
        let scale       ← match j.lookup? "scale" with
                          | none    => .ok none
                          | some sj => (decodeVec3 sj).map some
        let id          ← decodeIdField j
        return { translation, rotation, scale, id }
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  Soundness theorem

  Any NonemptyString in the decoded Transform's id satisfies val ≠ "".
  Proof: ns.nonempty is the struct field — no decoder tracing needed.
─────────────────────────────────────────────────────────────────────────────-/

theorem decodeTransform_sound
    (j : JsonValue) (t : Transform)
    (_h : decodeTransform j = .ok t) :
    ∀ ns, t.id = some ns → ns.val ≠ "" :=
  fun ns _ => ns.nonempty
