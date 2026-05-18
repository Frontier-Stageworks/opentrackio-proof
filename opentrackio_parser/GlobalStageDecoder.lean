/-
  GlobalStageDecoder.lean — Slice 14.2: globalstage-decoder

  Decoder for GlobalStage. All six fields are required JSON numbers
  stored as raw strings. No theorems.

  Ref: docs/laps/globalstage-decoder/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import SampleModel

def decodeGlobalStage (j : JsonValue) : Except DecodeError GlobalStage :=
  match j with
  | .object _ => do
      let E    ← match j.lookup? "E" with
                 | some (.number s) => .ok s
                 | none             => .error (.missingField "E")
                 | some _           => .error .expectedNumber
      let N    ← match j.lookup? "N" with
                 | some (.number s) => .ok s
                 | none             => .error (.missingField "N")
                 | some _           => .error .expectedNumber
      let U    ← match j.lookup? "U" with
                 | some (.number s) => .ok s
                 | none             => .error (.missingField "U")
                 | some _           => .error .expectedNumber
      let lat0 ← match j.lookup? "lat0" with
                 | some (.number s) => .ok s
                 | none             => .error (.missingField "lat0")
                 | some _           => .error .expectedNumber
      let lon0 ← match j.lookup? "lon0" with
                 | some (.number s) => .ok s
                 | none             => .error (.missingField "lon0")
                 | some _           => .error .expectedNumber
      let h0   ← match j.lookup? "h0" with
                 | some (.number s) => .ok s
                 | none             => .error (.missingField "h0")
                 | some _           => .error .expectedNumber
      return { E, N, U, lat0, lon0, h0 }
  | _ => .error .expectedObject
