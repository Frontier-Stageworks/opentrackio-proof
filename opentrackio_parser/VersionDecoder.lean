/-
  VersionDecoder.lean — Slice 4B: version-value-decoder

  Decodes a JsonValue into a ProtocolVersion and proves soundness.
  The input is expected to be a JSON array of exactly three integers in [0, 9].

  A12: JSON shape is .array of three .number elements.
  Ref: docs/laps/version-decoder/proof-capsule.md
-/

import Mathlib.Tactic
import DecodeError
import JsonRawModel
import ProtocolVersion

/-─────────────────────────────────────────────────────────────────────────────
  Digit decoder

  Accepts a JsonValue.number whose string is a natural number < 10.
  Rejects: non-number constructors (expectedNumber), out-of-range or
  non-numeric strings (invalidEnum).
─────────────────────────────────────────────────────────────────────────────-/

def decodeVersionDigit (j : JsonValue) : Except DecodeError VersionDigit :=
  match j with
  | .number s =>
    match s.toNat? with
    | some n => if h : n < 10 then .ok ⟨n, h⟩
                else .error (.invalidEnum "version" s)
    | none   => .error (.invalidEnum "version" s)
  | _ => .error .expectedNumber

/-─────────────────────────────────────────────────────────────────────────────
  Version value decoder

  Accepts a JsonValue.array of exactly three digit-valued elements.
  Rejects: wrong JSON constructor (expectedArray), wrong list length
  (invalidLength), and elements that fail decodeVersionDigit.
─────────────────────────────────────────────────────────────────────────────-/

def decodeVersionValue (j : JsonValue) : Except DecodeError ProtocolVersion :=
  match j with
  | .array [a, b, c] => do
      let major ← decodeVersionDigit a
      let minor ← decodeVersionDigit b
      let patch ← decodeVersionDigit c
      return { major, minor, patch }
  | .array xs => .error (.invalidLength "version" 3 xs.length)
  | _         => .error .expectedArray

/-─────────────────────────────────────────────────────────────────────────────
  Soundness theorem

  Any value returned by decodeVersionValue satisfies ValidVersion.

  The proof delegates to protocolVersion_valid: Fin 10 prevents construction
  of an out-of-range ProtocolVersion at the type level, so validity holds for
  any v regardless of which j produced it.
─────────────────────────────────────────────────────────────────────────────-/

theorem decodeVersionValue_sound
    (j : JsonValue) (v : ProtocolVersion)
    (_h : decodeVersionValue j = .ok v) :
    ValidVersion v :=
  protocolVersion_valid v
