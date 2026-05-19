# Slice 17 — Proof Capsule
# executable-differential-harness-packaging

**Status:** COMPLETE
**Date:** 2026-05-19

---

## Goal

Package the verified OpenTrackIO components (Slices 1–16) into a runnable Lean executable
that exercises decoder/encoder/normalization fixtures and exits 0 on all-pass or 1 on any
failure. Suitable as a CI smoke runner.

This is a packaging slice. No new theorems. No new proofs. No changes to Slices 1–16.

---

## Output

| Item | Value |
|---|---|
| File | `opentrackio_parser/HarnessMain.lean` |
| Lake target | `[[lean_exe]]` in `lakefile.toml` |
| Executable name | `opentrackio-harness` |
| Run command | `lake exe opentrackio-harness` |
| Imports | `NormalizationTheorems` (transitively pulls all of Slices 1–16) |

---

## Lake configuration

Add after the existing `[[lean_lib]]` entries and before `[[require]]`:

```toml
[[lean_exe]]
name = "opentrackio-harness"
srcDir = "opentrackio_parser"
root = "HarnessMain"
```

---

## Check structure

```lean
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

def main : IO UInt32 := runChecks checks
```

---

## Fixtures

### Decoder fixtures (mirror Slice 11.5 IntegrationSmoke)

```lean
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
  ("sampleId",  .string "cam1-0001"),
  ("sourceId",  .string "source-A"),
  ("protocol",  protocolJson)]
```

### Sample fixtures for roundtrip / normalization

```lean
-- All-optional-none shell: exercises the empty-object encode→decode path.
def sampleShell : Sample :=
  { globalStage := none, lens := none, protocol := none,
    relatedSampleIds := none, sampleId := none, sourceId := none,
    sourceNumber := none, «static» := none, timing := none,
    tracker := none, transforms := none }

-- Sample with two plain string fields: exercises string field encode→decode.
def sampleWithId : Sample :=
  { sampleShell with sampleId := some "cam1-0001", sourceId := some "source-A" }
```

---

## Check list

| # | Name | Expression |
|---|---|---|
| 1 | `protocol decoder` | `(decodeProtocol protocolJson).isOk` |
| 2 | `positive rational decoder` | `(decodePositiveRational rationalJson).isOk` |
| 3 | `transform decoder` | `(decodeTransform transformJson).isOk` |
| 4 | `camera decoder` | `(decodeCamera cameraJson).isOk` |
| 5 | `lens decoder` | `(decodeLens lensJson).isOk` |
| 6 | `sample decoder` | `(decodeSample sampleJson).isOk` |
| 7 | `roundtrip: empty sample` | `(decodeSample (encodeSample sampleShell)).isOk` |
| 8 | `roundtrip: sample with id` | `(decodeSample (encodeSample sampleWithId)).isOk` |
| 9 | `normalize: protocol-only json` | `(decodeSample (sampleNormalize sampleJson)).isOk` |
| 10 | `normalize: encoded shell` | `(decodeSample (sampleNormalize (encodeSample sampleShell))).isOk` |

Checks 7–8 exercise `encodeSample_roundtrip` at the executable level.
Checks 9–10 exercise `sampleNormalize` and `normalization_under_wellFormed` at the executable level.

---

## Expected output

```
PASS  protocol decoder
PASS  positive rational decoder
PASS  transform decoder
PASS  camera decoder
PASS  lens decoder
PASS  sample decoder
PASS  roundtrip: empty sample
PASS  roundtrip: sample with id
PASS  normalize: protocol-only json
PASS  normalize: encoded shell

all harness checks passed
```

Exit status 0.

---

## Hard step

Getting the `[[lean_exe]]` Lake configuration right. In particular:
- `root = "HarnessMain"` with `srcDir = "opentrackio_parser"` must resolve correctly
- `def main : IO UInt32` must be the accepted signature for a non-zero exit code
- All imports must be accessible (transitively via `NormalizationTheorems`)

---

## Scope boundaries

**AST-level only.** All fixtures use `JsonValue` constructors directly. No byte-level
JSON parsing. No stdin/file reading. No property-test generator. No Python/C++ differential
framework.

**No new theorems.** No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.

**No changes to Slices 1–16.**

---

## Stop 2 checklist (as delivered)

- [x] `HarnessMain.lean` created, elaborates under `lake build`
- [x] `scripts/opentrackio-harness.sh` created (wraps `lake env lean --run`)
- [x] `lake build` exits 0 (3290 jobs)
- [x] `lake env lean --run opentrackio_parser/HarnessMain.lean` prints all 10 PASS lines
- [x] No Slice 1–16 files modified
- [ ] `lake exe opentrackio-harness` native binary — deferred; Lean 4.29.0 bundled linker incompatible with Darwin 25.3.0 / SDK 26.5 (packaging/toolchain limitation, not a proof failure)
