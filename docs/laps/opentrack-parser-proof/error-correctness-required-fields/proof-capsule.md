# Proof Capsule — error-correctness-required-fields (Slice 13)

## Intent

Prove that each decoder returns `.error` when its required fields are absent.
This is soundness in the error direction: missing required input → decode fails.
No decoders are written or changed. No new types. Proofs only.

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/ErrorCorrectness.lean` | `ErrorCorrectness` |

One new `[[lean_lib]]` entry appended after `SampleDecoder` in `lakefile.toml`.

## Scope

Five theorems targeting three decoders with required fields:

| Decoder | Required field | Missing-field error |
|---|---|---|
| `decodeProtocol` | `"name"` | `.missingField "name"` |
| `decodeProtocol` | `"version"` (when name present) | `.missingField "version"` |
| `decodeTransform` | `"translation"` | `.missingField "translation"` |
| `decodeTransform` | `"rotation"` (when translation present) | `.missingField "rotation"` |
| `decodePositiveRational` | `"num"` | `.missingField "num"` |

`decodeNonemptyArray` empty-array rejection is already characterised by its
constructor (`| .array [] => .error ...`); it is excluded from this slice as
its error proof is `rfl` with no interesting content.

## Frozen formal statements

### T1 — Protocol missing name

```lean
theorem decodeProtocol_missing_name
    (kvs : List (String × JsonValue))
    (h : (JsonValue.object kvs).lookup? "name" = none) :
    decodeProtocol (.object kvs) = .error (.missingField "name")
```

### T2 — Protocol missing version

```lean
theorem decodeProtocol_missing_version
    (kvs : List (String × JsonValue))
    (name : String)
    (hn : (JsonValue.object kvs).lookup? "name" = some (.string name))
    (hv : (JsonValue.object kvs).lookup? "version" = none) :
    decodeProtocol (.object kvs) = .error (.missingField "version")
```

### T3 — Transform missing translation

```lean
theorem decodeTransform_missing_translation
    (kvs : List (String × JsonValue))
    (h : (JsonValue.object kvs).lookup? "translation" = none) :
    decodeTransform (.object kvs) = .error (.missingField "translation")
```

### T4 — Transform missing rotation

```lean
theorem decodeTransform_missing_rotation
    (kvs : List (String × JsonValue))
    (tj : JsonValue)
    (ht : (JsonValue.object kvs).lookup? "translation" = some tj)
    (hr : (JsonValue.object kvs).lookup? "rotation" = none) :
    decodeTransform (.object kvs) = .error (.missingField "rotation")
```

### T5 — Positive rational missing num

```lean
theorem decodePositiveRational_missing_num
    (kvs : List (String × JsonValue))
    (h : (JsonValue.object kvs).lookup? "num" = none) :
    decodePositiveRational (.object kvs) = .error (.missingField "num")
```

## Proof strategy

Each decoder pattern-matches on `lookup?` results before doing any monadic
work. Substituting the hypothesis into the match reduces the goal to `.error X = .error X`,
closed by `rfl` or `simp`. Expected tactic: `simp [decoderName, h1, h2, ...]`.
If simp cannot reduce through the match, fall back to `unfold` + `rw` + `rfl`.

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No `open Classical`.
- No new decoders, structs, or types.
- No changes to Slices 1–12B.

## Stop rule

If any theorem fails, diagnose that single theorem before touching others.
If `simp` cannot close a goal, stop and report — do not attempt more than
one alternative tactic before reporting back.

## Acceptance criteria

1. `lake env lean opentrackio_parser/ErrorCorrectness.lean` — exit 0, no warnings.
2. `lake build ErrorCorrectness` — exit 0.
3. All five theorems proved without `sorry`.
