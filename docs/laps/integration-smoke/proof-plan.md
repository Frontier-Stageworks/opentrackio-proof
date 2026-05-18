# Proof Plan — integration-smoke (Slice 12-pre)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/IntegrationSmoke.lean` | `IntegrationSmoke` |

One new `[[lean_lib]]` entry appended after `SampleModel` in `lakefile.toml`.

---

## Capsule correction

The capsule's `decodeProtocol` example omitted the required `"name"` field.
`decodeProtocol` takes the protocol sub-object (not the outer sample object);
it expects `{"name": string, "version": array}`. The plan corrects the JSON.

The capsule's `#eval native_decide (P)` phrasing is not valid Lean 4 term
syntax (`native_decide` is a tactic). The plan uses `#eval expr |>.isOk`
which evaluates the `Bool` directly and prints `true` or `false`.

---

## Step 1 — Lakefile

Append to `lakefile.toml`:

```toml
[[lean_lib]]
name = "IntegrationSmoke"
srcDir = "opentrackio_parser"
```

---

## Step 2 — File header and imports

```lean
/-
  IntegrationSmoke.lean — integration smoke test

  Verifies that all 16 parser modules (Slices 1–11) compose without
  elaboration failure. No new theorems. No sorry. No changes to Slices 1–11.
-/

import RationalValueWrappers
import JsonRawModel
import DecodeError
import ProtocolVersion
import VersionDecoder
import ProtocolDecoder
import RationalDecoder
import NonemptyArrayDecoder
import TimingEnumDecoders
import TransformModel
import TransformDecoder
import CameraModel
import CameraDecoder
import LensModel
import LensDecoder
import SampleModel
```

---

## Step 3 — Component 1: Protocol decode

```lean
-- Protocol sub-object: name required; version array of 3 digits.
#eval decodeProtocol (.object [
  ("name",    .string "OpenTrackIO"),
  ("version", .array [.number "1", .number "0", .number "1"])
]) |>.isOk
-- Expected output: true
```

---

## Step 4 — Component 2: Positive rational decode

```lean
-- num and denom are positive; toReal > 0.
#eval decodePositiveRational (.object [
  ("num",   .number "24000"),
  ("denom", .number "1001")
]) |>.isOk
-- Expected output: true
```

---

## Step 5 — Component 3: Transform decode

```lean
-- translation and rotation required; id optional nonempty string.
#eval decodeTransform (.object [
  ("translation", .object [("x", .number "1"), ("y", .number "0"), ("z", .number "0")]),
  ("rotation",    .object [("pan", .number "0"), ("tilt", .number "0"), ("roll", .number "0")]),
  ("id",          .string "cam1")
]) |>.isOk
-- Expected output: true
```

---

## Step 6 — Component 4: Camera decode

```lean
-- captureFrameRate → PositiveRational; make → NonemptyString.
#eval decodeCamera (.object [
  ("captureFrameRate", .object [("num", .number "24"), ("denom", .number "1")]),
  ("make",             .string "ARRI")
]) |>.isOk
-- Expected output: true
```

---

## Step 7 — Component 5: Lens encoders anyPresent invariant

```lean
-- encoders with focus/iris/zoom all present → FizOptions.anyPresent holds.
#eval decodeLens (.object [
  ("encoders", .object [
    ("focus", .number "0.5"),
    ("iris",  .number "0.3"),
    ("zoom",  .number "0.1")
  ])
]) |>.isOk
-- Expected output: true
```

---

## Step 8 — Shell construction

`Except.toOption` extracts `Option α` from decoder results. The `«static»`
field uses `Option.map` to thread the camera value into `StaticInfo`.

```lean
def smokeSample : Sample :=
  let cOpt := (decodeCamera (.object [("make", .string "ARRI")])).toOption
  let lOpt := (decodeLens (.object [
    ("encoders", .object [
      ("focus", .number "0.5"),
      ("iris",  .number "0.3"),
      ("zoom",  .number "0.1")
    ])
  ])).toOption
  { globalStage      := none
    lens             := lOpt
    protocol         := none
    relatedSampleIds := none
    sampleId         := none
    sourceId         := none
    sourceNumber     := none
    «static»         := cOpt.map (fun c =>
                          { camera  := some c
                            duration := none
                            lens     := none
                            tracker  := none })
    timing           := none
    tracker          := none
    transforms       := none }
```

---

## Stop rule

At the first elaboration failure, stop. Diagnose the single failing item.
Do not attempt more than one workaround before reporting.

Likely failure modes and first-line diagnosis:
- Unknown identifier → wrong import or name mismatch with actual Lean name
- `#eval` timeout → decoder is not computable; inspect for `noncomputable`
- `«static»` field not found → try `static` without guillemets to test
- `toOption` not in scope → use `match ... with | .ok v => some v | .error _ => none`

---

## Acceptance criteria

1. `lake env lean opentrackio_parser/IntegrationSmoke.lean` — exit 0, no warnings.
2. `lake build IntegrationSmoke` — exit 0.
3. All five `#eval` lines print `true`.
4. `smokeSample` elaborates without `sorry`.
5. No changes to any file in Slices 1–11.
