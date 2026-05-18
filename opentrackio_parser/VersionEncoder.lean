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
