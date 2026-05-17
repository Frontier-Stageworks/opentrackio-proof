/-
  ProtocolDecoder.lean — Slice 4C: protocol-version-field-decoder

  Decodes a JsonValue (the protocol sub-object) into a ProtocolInfo and
  proves that the decoded version satisfies ValidVersion.

  A8: sub-field keys are "name" (string, required) and "version" (array, required).
  Both fields are required when the protocol object is present.
  Ref: docs/laps/protocol-decoder/proof-capsule.md
-/

import Mathlib.Tactic
import DecodeError
import JsonRawModel
import ProtocolVersion
import VersionDecoder

/-─────────────────────────────────────────────────────────────────────────────
  ProtocolInfo

  Holds the decoded name (String) and version (ProtocolVersion) from the
  protocol sub-object.
─────────────────────────────────────────────────────────────────────────────-/

structure ProtocolInfo where
  name    : String
  version : ProtocolVersion

/-─────────────────────────────────────────────────────────────────────────────
  Protocol decoder

  Accepts a JsonValue.object with required "name" (string) and "version"
  (array of 3 digits, decoded by decodeVersionValue).
─────────────────────────────────────────────────────────────────────────────-/

def decodeProtocol (j : JsonValue) : Except DecodeError ProtocolInfo :=
  match j with
  | .object _ =>
    match j.lookup? "name" with
    | none    => .error (.missingField "name")
    | some nj =>
      match nj with
      | .string n =>
        match j.lookup? "version" with
        | none    => .error (.missingField "version")
        | some vj => do
            let v ← decodeVersionValue vj
            return { name := n, version := v }
      | _ => .error .expectedString
  | _ => .error .expectedObject

/-─────────────────────────────────────────────────────────────────────────────
  Soundness theorem

  Any ProtocolInfo returned by decodeProtocol has a valid version.

  The proof delegates to protocolVersion_valid: Fin 10 prevents construction
  of an out-of-range ProtocolVersion, so ValidVersion holds for any v.
─────────────────────────────────────────────────────────────────────────────-/

theorem decodeProtocol_sound
    (j : JsonValue) (p : ProtocolInfo)
    (_h : decodeProtocol j = .ok p) :
    ValidVersion p.version :=
  protocolVersion_valid p.version
