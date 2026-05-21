# Proof Capsule — integration-smoke (Slice 12-pre)

## Intent

Verify that all 16 parser modules (Slices 1–11) compose without elaboration
failures, that invariant-carrying types survive decode round-trips, and that
`Sample` can be shell-constructed from decoder outputs. This is a compile-time
integration check, not a runtime test harness.

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/IntegrationSmoke.lean` | `IntegrationSmoke` |

One new `[[lean_lib]]` entry appended after `SampleModel` in `lakefile.toml`.

## Imports (all 16 parser modules)

```lean
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

## Frozen formal statements

### Component 1 — Protocol version decode

```lean
#eval native_decide (decodeProtocol (.object [("protocol", .object [("version", .array [.number "1", .number "0", .number "1"])])]) |>.isOk = true)
```

Acceptance: evaluates to `true`.

### Component 2 — Positive rational decode

```lean
#eval native_decide (decodePositiveRational (.object [("num", .number "24000"), ("denom", .number "1001")]) |>.isOk = true)
```

Acceptance: evaluates to `true`.

### Component 3 — Transform decode

```lean
#eval native_decide (decodeTransform (.object [
  ("translation", .object [("x", .number "1"), ("y", .number "0"), ("z", .number "0")]),
  ("rotation", .object [("pan", .number "0"), ("tilt", .number "0"), ("roll", .number "0")]),
  ("id", .string "cam1")
]) |>.isOk = true)
```

Acceptance: evaluates to `true`.

### Component 4 — Camera decode with invariant-carrying field

```lean
#eval native_decide (decodeCamera (.object [
  ("captureFrameRate", .object [("num", .number "24"), ("denom", .number "1")]),
  ("make", .string "ARRI")
]) |>.isOk = true)
```

Acceptance: evaluates to `true`. The returned `Camera` holds a `PositiveRational`
and a `NonemptyString`; both invariants are enforced at type level.

### Component 5 — Lens encoders anyPresent invariant

```lean
#eval native_decide (decodeLens (.object [
  ("encoders", .object [("focus", .number "0.5"), ("iris", .number "0.3"), ("zoom", .number "0.1")])
]) |>.isOk = true)
```

Acceptance: evaluates to `true`. The `FizOptions.anyPresent` proof field is
carried in the returned struct; no separate check needed.

### Component 6 — Shell Sample construction

```lean
def smokeSample : Sample :=
  match decodeCamera (.object [("make", .string "ARRI")]) with
  | .ok c =>
    match decodeLens (.object [("encoders", .object [("focus", .number "0.5"), ("iris", .number "0.3"), ("zoom", .number "0.1")])]) with
    | .ok l => { lens := some l, «static» := some { camera := some c, duration := none, lens := none, tracker := none }, globalStage := none, protocol := none, relatedSampleIds := none, sampleId := none, sourceId := none, sourceNumber := none, timing := none, tracker := none, transforms := none }
    | .error _ => { lens := none, «static» := none, globalStage := none, protocol := none, relatedSampleIds := none, sampleId := none, sourceId := none, sourceNumber := none, timing := none, tracker := none, transforms := none }
  | .error _ => { lens := none, «static» := none, globalStage := none, protocol := none, relatedSampleIds := none, sampleId := none, sourceId := none, sourceNumber := none, timing := none, tracker := none, transforms := none }
```

Acceptance: elaborates without error. No `sorry`. No proofs asserted.

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No `open Classical`.
- No new theorems.
- No changes to Slices 1–11 (all 16 existing files are read-only).
- No `#check` substituting for `#eval native_decide`.

## Tactic and evaluation strategy

- All `#eval native_decide (... |>.isOk = true)` propositions rely on
  `Decidable` instances already in scope; `native_decide` compiles to native
  code and avoids the kernel reduction ceiling.
- `smokeSample` is a plain `def`, not a theorem; elaboration is the acceptance
  criterion.

## Stop rule

At the first elaboration failure (unknown identifier, type mismatch, or
`native_decide` timeout), stop. Diagnose the single failing item. Do not
attempt more than one fix before reporting back.

## Acceptance criteria

1. `lake env lean opentrackio_parser/IntegrationSmoke.lean` — exit 0, no warnings.
2. `lake build IntegrationSmoke` — exit 0.
3. All five `#eval native_decide` lines print `true`.
4. `smokeSample` elaborates without `sorry`.
5. No changes to Slices 1–11.
