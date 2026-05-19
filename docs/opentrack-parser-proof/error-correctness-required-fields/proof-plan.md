# Proof Plan — error-correctness-required-fields (Slice 13)

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/ErrorCorrectness.lean` | `ErrorCorrectness` |

Appended after `SampleDecoder` in `lakefile.toml`.

---

## Step 1 — Lakefile

```toml
[[lean_lib]]
name = "ErrorCorrectness"
srcDir = "opentrackio_parser"
```

---

## Step 2 — File header and imports

```lean
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
```

---

## Step 3 — Five theorems

### T1 — Protocol missing name

```lean
theorem decodeProtocol_missing_name
    (kvs : List (String × JsonValue))
    (h : (JsonValue.object kvs).lookup? "name" = none) :
    decodeProtocol (.object kvs) = .error (.missingField "name") := by
  simp [decodeProtocol, h]
```

`simp` unfolds `decodeProtocol`, matches `.object _`, substitutes `h` into
the `lookup? "name"` branch, and the `none` arm reduces to
`.error (.missingField "name") = .error (.missingField "name")`.

### T2 — Protocol missing version

```lean
theorem decodeProtocol_missing_version
    (kvs : List (String × JsonValue))
    (name : String)
    (hn : (JsonValue.object kvs).lookup? "name" = some (.string name))
    (hv : (JsonValue.object kvs).lookup? "version" = none) :
    decodeProtocol (.object kvs) = .error (.missingField "version") := by
  simp [decodeProtocol, hn, hv]
```

`simp` unfolds `decodeProtocol`, the `name` match resolves via `hn` to the
`.string` branch, then `hv` collapses the `version` lookup to `none`.

### T3 — Transform missing translation

```lean
theorem decodeTransform_missing_translation
    (kvs : List (String × JsonValue))
    (h : (JsonValue.object kvs).lookup? "translation" = none) :
    decodeTransform (.object kvs) = .error (.missingField "translation") := by
  simp [decodeTransform, h]
```

### T4 — Transform missing rotation

```lean
theorem decodeTransform_missing_rotation
    (kvs : List (String × JsonValue))
    (tj : JsonValue)
    (ht : (JsonValue.object kvs).lookup? "translation" = some tj)
    (hr : (JsonValue.object kvs).lookup? "rotation" = none) :
    decodeTransform (.object kvs) = .error (.missingField "rotation") := by
  simp [decodeTransform, ht, hr]
```

### T5 — Positive rational missing num

```lean
theorem decodePositiveRational_missing_num
    (kvs : List (String × JsonValue))
    (h : (JsonValue.object kvs).lookup? "num" = none) :
    decodePositiveRational (.object kvs) = .error (.missingField "num") := by
  simp [decodePositiveRational, h]
```

`decodePositiveRational` uses a simultaneous `match lookup? "num", lookup? "denom"`.
`simp` should substitute `none` for the first component, collapsing to the
`| none, _ =>` arm. If simp cannot handle the simultaneous match, fallback:

```lean
  unfold decodePositiveRational
  rw [h]
```

---

## Stop rule

Write all five theorems. If any fails, fix only that theorem before proceeding
to the next. Do not try more than one alternative tactic per failure before
reporting back.

## Acceptance criteria

1. `lake env lean opentrackio_parser/ErrorCorrectness.lean` — exit 0, no warnings.
2. `lake build ErrorCorrectness` — exit 0.
3. All five theorems proved without `sorry`.
