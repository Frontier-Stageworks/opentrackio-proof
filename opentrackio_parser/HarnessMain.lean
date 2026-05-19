/-
  HarnessMain.lean — Slice 17: executable-differential-harness-packaging

  Runnable executable that exercises the verified OpenTrackIO components.
  All fixtures operate over JsonValue AST constructors — no byte-level JSON parsing.
  Exits 0 if all checks pass; exits 1 if any check fails.

  Run with:  lake exe opentrackio-harness

  Ref: docs/opentrack-parser-proof/executable-harness/proof-capsule.md
-/

import NormalizationTheorems

/-─────────────────────────────────────────────────────────────────────────────
  Check type and runner
─────────────────────────────────────────────────────────────────────────────-/

def Check := String × Bool

def printCheck (c : Check) : IO Unit :=
  if c.2 then IO.println s!"PASS  {c.1}"
  else        IO.println s!"FAIL  {c.1}"

def runChecks (cs : List Check) : IO UInt32 := do
  cs.forM printCheck
  if cs.all (·.2) then
    IO.println "\nall harness checks passed"
    return 0
  else
    IO.eprintln "\none or more harness checks failed"
    return 1

/-─────────────────────────────────────────────────────────────────────────────
  Decoder fixtures (mirror Slice 11.5 IntegrationSmoke)
─────────────────────────────────────────────────────────────────────────────-/

def protocolJson : JsonValue := .object [
  ("name",    .string "OpenTrackIO"),
  ("version", .array [.number "1", .number "0", .number "1"])]

def rationalJson : JsonValue := .object [
  ("num", .number "24000"), ("denom", .number "1001")]

def transformJson : JsonValue := .object [
  ("translation", .object [("x", .number "1"), ("y", .number "0"), ("z", .number "0")]),
  ("rotation",    .object [("pan", .number "0"), ("tilt", .number "0"), ("roll", .number "0")]),
  ("id",          .string "cam1")]

def cameraJson : JsonValue := .object [
  ("captureFrameRate", .object [("num", .number "24"), ("denom", .number "1")]),
  ("make",             .string "ARRI")]

def lensJson : JsonValue := .object [
  ("encoders", .object [
    ("focus", .number "0.5"),
    ("iris",  .number "0.3"),
    ("zoom",  .number "0.1")])]

def sampleJson : JsonValue := .object [
  ("sampleId", .string "cam1-0001"),
  ("sourceId", .string "source-A"),
  ("protocol", protocolJson)]

/-─────────────────────────────────────────────────────────────────────────────
  Sample fixtures for roundtrip and normalization checks
─────────────────────────────────────────────────────────────────────────────-/

-- All-optional-none shell: exercises the empty-object encode→decode path.
def sampleShell : Sample :=
  { globalStage      := none
    lens             := none
    protocol         := none
    relatedSampleIds := none
    sampleId         := none
    sourceId         := none
    sourceNumber     := none
    «static»         := none
    timing           := none
    tracker          := none
    transforms       := none }

-- Sample with two plain string fields: exercises string-field encode→decode.
def sampleWithId : Sample :=
  { sampleShell with sampleId := some "cam1-0001", sourceId := some "source-A" }

/-─────────────────────────────────────────────────────────────────────────────
  Check list
─────────────────────────────────────────────────────────────────────────────-/

def checks : List Check := [
  -- Decoder fixtures
  ("protocol decoder",          (decodeProtocol protocolJson).isOk),
  ("positive rational decoder", (decodePositiveRational rationalJson).isOk),
  ("transform decoder",         (decodeTransform transformJson).isOk),
  ("camera decoder",            (decodeCamera cameraJson).isOk),
  ("lens decoder",              (decodeLens lensJson).isOk),
  ("sample decoder",            (decodeSample sampleJson).isOk),
  -- Encoder/decoder roundtrip (exercises encodeSample_roundtrip at runtime)
  ("roundtrip: empty sample",   (decodeSample (encodeSample sampleShell)).isOk),
  ("roundtrip: sample with id", (decodeSample (encodeSample sampleWithId)).isOk),
  -- Normalization (exercises sampleNormalize at runtime)
  ("normalize: protocol-only json", (decodeSample (sampleNormalize sampleJson)).isOk),
  ("normalize: encoded shell",      (decodeSample (sampleNormalize (encodeSample sampleShell))).isOk)]

/-─────────────────────────────────────────────────────────────────────────────
  Entry point
─────────────────────────────────────────────────────────────────────────────-/

def main : IO UInt32 := runChecks checks
