/-
  ErrorCorrectness.lean — Slice 13: error-correctness-required-fields

  Proves that each decoder returns .error when its required fields are
  absent. Soundness in the error direction: missing required input → decode
  fails. No new decoders, structs, or types.

  Ref: docs/laps/error-correctness-required-fields/proof-capsule.md
-/

import Mathlib.Tactic
import DecodeError
import JsonRawModel
import RationalDecoder
import TransformDecoder
import ProtocolDecoder

theorem decodeProtocol_missing_name
    (kvs : List (String × JsonValue))
    (h : (JsonValue.object kvs).lookup? "name" = none) :
    decodeProtocol (.object kvs) = .error (.missingField "name") := by
  simp [decodeProtocol, h]

theorem decodeProtocol_missing_version
    (kvs : List (String × JsonValue))
    (name : String)
    (hn : (JsonValue.object kvs).lookup? "name" = some (.string name))
    (hv : (JsonValue.object kvs).lookup? "version" = none) :
    decodeProtocol (.object kvs) = .error (.missingField "version") := by
  simp [decodeProtocol, hn, hv]

theorem decodeTransform_missing_translation
    (kvs : List (String × JsonValue))
    (h : (JsonValue.object kvs).lookup? "translation" = none) :
    decodeTransform (.object kvs) = .error (.missingField "translation") := by
  simp [decodeTransform, h]

theorem decodeTransform_missing_rotation
    (kvs : List (String × JsonValue))
    (tj : JsonValue)
    (ht : (JsonValue.object kvs).lookup? "translation" = some tj)
    (hr : (JsonValue.object kvs).lookup? "rotation" = none) :
    decodeTransform (.object kvs) = .error (.missingField "rotation") := by
  simp [decodeTransform, ht, hr]

theorem decodePositiveRational_missing_num
    (kvs : List (String × JsonValue))
    (h : (JsonValue.object kvs).lookup? "num" = none) :
    decodePositiveRational (.object kvs) = .error (.missingField "num") := by
  simp [decodePositiveRational, h]
