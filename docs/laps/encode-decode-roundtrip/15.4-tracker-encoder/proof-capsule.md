# Proof Capsule — tracker-encoder (Slice 15.4)

## Intent

Define `encodeStaticTracker : StaticTracker → JsonValue` and
`encodeTracker : Tracker → JsonValue`, and prove roundtrip theorems for each.

`StaticTracker` has four optional `NonemptyString` fields.
`Tracker` has three optional `NonemptyString` fields and one optional `Bool` field.
Both decoders use the private `decodeOptionalString` pattern with
`if h : s ≠ "" then .ok (some ⟨s, h⟩)`.

## File and lakefile entry

| File | Library name |
|---|---|
| `opentrackio_parser/TrackerEncoder.lean` | `TrackerEncoder` |

One new `[[lean_lib]]` entry appended after `GlobalStageEncoder` in `lakefile.toml`.

## Imports

```lean
import DecodeError
import JsonRawModel
import TransformModel
import SampleModel
import TrackerDecoder
```

## Frozen formal statements

```lean
def encodeStaticTracker (st : StaticTracker) : JsonValue
def encodeTracker       (t  : Tracker)       : JsonValue

theorem encodeStaticTracker_roundtrip (st : StaticTracker) :
    decodeStaticTracker (encodeStaticTracker st) = .ok st

theorem encodeTracker_roundtrip (t : Tracker) :
    decodeTracker (encodeTracker t) = .ok t
```

## Encoder specification

Optional `NonemptyString` fields are encoded as `.string ns.val` when present,
omitted when absent. Optional `Bool` fields use `.bool b`.

```
encodeStaticTracker st = .object (
  (st.make.map            fun ns => ("make",            .string ns.val)).toList ++
  (st.model.map           fun ns => ("model",           .string ns.val)).toList ++
  (st.serialNumber.map    fun ns => ("serialNumber",    .string ns.val)).toList ++
  (st.firmwareVersion.map fun ns => ("firmwareVersion", .string ns.val)).toList
)

encodeTracker t = .object (
  (t.notes.map     fun ns => ("notes",     .string ns.val)).toList ++
  (t.recording.map fun b  => ("recording", .bool b)).toList         ++
  (t.slate.map     fun ns => ("slate",     .string ns.val)).toList  ++
  (t.status.map    fun ns => ("status",    .string ns.val)).toList
)
```

## Proof strategy

Use `rcases` to simultaneously `cases` and destructure `NonemptyString`:

```lean
rcases mk with _ | ⟨mkv, mkh⟩ <;> ...
```

This exposes `mkh : mkv ≠ ""` directly in the `some` branch. Then
`simp [encode, decode, JsonValue.lookup?, decodeOptionalString, *]`
uses `*` to include `mkh` etc. as hypotheses, which allows the
`dite (mkv ≠ "") ...` in `decodeOptionalString` to reduce. Append
`; rfl` for any residual `Except.bind` chain.

## Forbidden constructs

- No `sorry`, `admit`, `axiom`, `unsafe`, `partial`.
- No new struct definitions.
- No changes to Slices 1–14.8.

## Stop rule

At the first elaboration failure, stop and diagnose before attempting any fix.

## Acceptance criteria

1. `lake env lean opentrackio_parser/TrackerEncoder.lean` — exit 0, no warnings.
2. `lake build TrackerEncoder` — exit 0.
3. No `sorry` or forbidden constructs.
4. Both roundtrip theorems green.
