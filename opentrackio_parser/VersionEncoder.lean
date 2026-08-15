/-
  VersionEncoder.lean — Slice 14: encoder-version

  Encoders for ProtocolVersion and ProtocolInfo, and encode-then-decode
  roundtrip theorems. No new types. No changes to existing decoders.

  Ref: docs/laps/encoder-version/proof-capsule.md
-/

import Mathlib.Tactic
import DecodeError
import JsonRawModel
import ProtocolVersion
import VersionDecoder
import ProtocolDecoder

def encodeVersionDigit (d : VersionDigit) : JsonValue :=
  .number (toString d.val)

def encodeVersionValue (v : ProtocolVersion) : JsonValue :=
  .array [encodeVersionDigit v.major, encodeVersionDigit v.minor, encodeVersionDigit v.patch]

def encodeProtocol (p : ProtocolInfo) : JsonValue :=
  .object [("name", .string p.name), ("version", encodeVersionValue p.version)]

/-
  encodeVersionDigit_roundtrip uses native_decide rather than decide.

  The roundtrip crosses a string boundary: encodeVersionDigit calls toString d.val
  (producing "0"–"9"), and decodeVersionDigit calls String.toNat? to parse it back.
  Both are native runtime primitives that the Lean kernel evaluator cannot reduce.
  decide gets stuck before it can close the goal; native_decide compiles and runs
  each of the 10 closed ground terms instead.

  Trust implication: this theorem's axiom set includes Lean.ofReduceBool (the
  native-decide axiom) in addition to the standard propext / Classical.choice /
  Quot.sound. The correctness of the roundtrip therefore depends on the Lean native
  compiler faithfully implementing toString and String.toNat? — not only the kernel.
  This is the accepted trade-off for string-boundary computations in Lean 4 / Mathlib.
-/
theorem encodeVersionDigit_roundtrip (d : VersionDigit) :
    decodeVersionDigit (encodeVersionDigit d) = .ok d := by
  fin_cases d <;> native_decide

theorem encodeVersionValue_roundtrip (v : ProtocolVersion) :
    decodeVersionValue (encodeVersionValue v) = .ok v := by
  simp [decodeVersionValue, encodeVersionValue, encodeVersionDigit_roundtrip]
  rfl

theorem encodeProtocol_roundtrip (p : ProtocolInfo) :
    decodeProtocol (encodeProtocol p) = .ok p := by
  simp [decodeProtocol, encodeProtocol, JsonValue.lookup?,
        encodeVersionValue_roundtrip]
