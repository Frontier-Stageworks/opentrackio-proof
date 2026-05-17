/-
  RationalDecoder.lean — Slice 5: rational-decoder-soundness

  Decodes a JsonValue of the form { "num": ..., "denom": ... } into a
  PositiveRational and proves that any successfully decoded value is positive.

  A1: rational fields are objects with "num" and "denom" integer sub-fields.
  A7: positivity invariants live in the type; soundness delegates to Slice 1.
  Ref: docs/laps/rational-decoder/proof-capsule.md
-/

import Mathlib.Tactic
import DecodeError
import JsonRawModel
import RationalValueWrappers

/-─────────────────────────────────────────────────────────────────────────────
  Rational decoder

  Accepts a JsonValue.object with required "num" and "denom" sub-fields.
  Each must be a JsonValue.number whose string parses as a positive Nat.
  The positivity proofs become the struct fields num_pos and den_pos.
─────────────────────────────────────────────────────────────────────────────-/

def decodePositiveRational (j : JsonValue) : Except DecodeError PositiveRational :=
  match j with
  | .object _ =>
    match j.lookup? "num", j.lookup? "denom" with
    | none, _          => .error (.missingField "num")
    | _, none          => .error (.missingField "denom")
    | some nj, some dj =>
      match nj, dj with
      | .number ns, .number ds =>
        match ns.toNat?, ds.toNat? with
        | some n, some d =>
          if hn : 0 < n then
            if hd : 0 < d then .ok { num := n, den := d, num_pos := hn, den_pos := hd }
            else .error (.invalidRational "denom")
          else .error (.invalidRational "num")
        | none, _ => .error (.invalidRational "num")
        | _, none => .error (.invalidRational "denom")
      | .number _, _ => .error .expectedNumber
      | _, _         => .error .expectedNumber
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  Soundness theorem

  Any PositiveRational returned by decodePositiveRational has a positive
  real value.

  The proof delegates to positive_rational_toReal_pos (Slice 1): any
  r : PositiveRational satisfies 0 < r.toReal by the num_pos and den_pos
  struct fields. The decoder hypothesis is intentionally unused.
─────────────────────────────────────────────────────────────────────────────-/

theorem decodePositiveRational_sound
    (j : JsonValue) (r : PositiveRational)
    (_h : decodePositiveRational j = .ok r) :
    0 < r.toReal :=
  positive_rational_toReal_pos r
