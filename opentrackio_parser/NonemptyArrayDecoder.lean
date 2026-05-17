/-
  NonemptyArrayDecoder.lean — Slice 6: nonempty-array-decoder

  Defines NonemptyArray α, a generic nonempty-list wrapper, and a decoder that
  accepts a JSON array with at least one element. Proves that any successfully
  decoded value satisfies the nonemptiness invariant.

  A6: OpenTrackIO numeric arrays have minItems = 1, no maxItems — no fixed length.
  Ref: docs/laps/nonempty-array-decoder/proof-capsule.md
-/

import Mathlib.Tactic
import DecodeError
import JsonRawModel

/-─────────────────────────────────────────────────────────────────────────────
  NonemptyArray

  A List α together with a proof that it is not empty.
  Used for protocol fields that require at least one element (minItems = 1).
─────────────────────────────────────────────────────────────────────────────-/

structure NonemptyArray (α : Type) where
  values   : List α
  nonempty : values ≠ []

/-─────────────────────────────────────────────────────────────────────────────
  Nonempty array decoder

  Accepts a JsonValue.array with at least one element.
  Decodes each element using the caller-supplied decodeElem function.
  Rejects: non-array (expectedArray), empty array (invalidLength).
─────────────────────────────────────────────────────────────────────────────-/

def decodeNonemptyArray
    (decodeElem : JsonValue → Except DecodeError α)
    (context : String)
    (j : JsonValue) : Except DecodeError (NonemptyArray α) :=
  match j with
  | .array []         => .error (.invalidLength context 1 0)
  | .array (hd :: tl) => do
      let v  ← decodeElem hd
      let vs ← tl.mapM decodeElem
      return { values := v :: vs, nonempty := List.cons_ne_nil v vs }
  | _                 => .error .expectedArray

/-─────────────────────────────────────────────────────────────────────────────
  Soundness theorem

  Any NonemptyArray returned by decodeNonemptyArray satisfies the nonemptiness
  invariant. The proof reads out the struct field directly; the decoder
  hypothesis is intentionally unused.
─────────────────────────────────────────────────────────────────────────────-/

theorem decodeNonemptyArray_sound
    (decodeElem : JsonValue → Except DecodeError α)
    (context : String) (j : JsonValue) (arr : NonemptyArray α)
    (_h : decodeNonemptyArray decodeElem context j = .ok arr) :
    arr.values ≠ [] :=
  arr.nonempty
