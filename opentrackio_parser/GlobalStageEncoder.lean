/-
  GlobalStageEncoder.lean — Slice 15.3: globalstage-encoder

  Encoder for GlobalStage with roundtrip theorem.
  Six required number fields; no optional fields or invariant-carrying types.

  Ref: docs/laps/encode-decode-roundtrip/15.3-globalstage-encoder/proof-capsule.md
-/

import DecodeError
import JsonRawModel
import SampleModel
import GlobalStageDecoder

def encodeGlobalStage (g : GlobalStage) : JsonValue :=
  .object [("E",    .number g.E),
           ("N",    .number g.N),
           ("U",    .number g.U),
           ("lat0", .number g.lat0),
           ("lon0", .number g.lon0),
           ("h0",   .number g.h0)]

theorem encodeGlobalStage_roundtrip (g : GlobalStage) :
    decodeGlobalStage (encodeGlobalStage g) = .ok g := by
  simp [encodeGlobalStage, decodeGlobalStage, JsonValue.lookup?]; rfl
