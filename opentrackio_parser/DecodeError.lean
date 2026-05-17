/-
  DecodeError.lean — Slice 3: decode-error-vocabulary

  Structured reasons a decoder can reject input.
  This is a pure definition file; no decoder or protocol model.

  Ref: docs/laps/opentrack-parser-verification/first-slice-contract.md
  A2:  `duplicateKey` added because duplicate keys are a decoding error
       under the resolved A2 policy.
-/

inductive DecodeError where
  | expectedObject
  | expectedArray
  | expectedString
  | expectedNumber
  | missingField    : String → DecodeError
  | duplicateKey    : String → DecodeError
  | invalidRational : String → DecodeError
  | invalidEnum     : String → String → DecodeError
  | invalidLength   : String → Nat → Nat → DecodeError
  deriving Repr, DecidableEq
